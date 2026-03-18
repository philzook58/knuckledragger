import importlib
import itertools
import os
import pkgutil
import time

import kdrag as kd
import kdrag.config as config


def discover_theory_modules() -> list[str]:
    theories = importlib.import_module("kdrag.theories")
    discovered: list[str] = []
    for module in pkgutil.walk_packages(theories.__path__, "kdrag.theories."):
        if module.ispkg:
            continue
        module_name = module.name
        if module_name.split(".")[-1].startswith("_"):
            continue
        discovered.append(module_name)
    return sorted(discovered)


if __name__ == "__main__":
    config.timing = True
    module_times: list[tuple[float, str]] = []
    import_failures: list[tuple[str, str]] = []

    def import_and_time(module_name: str, start_time: float) -> float:
        importlib.import_module(module_name)
        end_time = time.perf_counter()
        module_times.append((end_time - start_time, module_name))
        return end_time

    start_time = time.perf_counter()

    start_time = import_and_time("kdrag.all", start_time)
    for module_name in discover_theory_modules():
        try:
            start_time = import_and_time(module_name, start_time)
        except Exception as exc:
            import_failures.append((module_name, repr(exc)))

    print("\n========= Module import times ========\n")
    for elapsed_time, tag in sorted(module_times, reverse=True):
        print(f"{elapsed_time:.6f} {tag}")

    if import_failures:
        print("\n========= Import failures (non-fatal) ========\n")
        for module_name, error in import_failures:
            print(f"{module_name}: {error}")
        if os.environ.get("KDRAG_PERF_STRICT_IMPORTS", "0") == "1":
            raise RuntimeError("Module import failures encountered in strict mode")

    for tag, group in itertools.groupby(
        sorted(config.perf_log, key=lambda x: x[0]), key=lambda x: x[0]
    ):
        print("\n=============" + tag + "=============\n")
        for tag, data, entry_time in sorted(group, key=lambda x: x[2], reverse=True)[:20]:
            print(f"{entry_time:.6f}: {data}")

    kd.utils.write_smt2_files("/tmp/kdrag")
