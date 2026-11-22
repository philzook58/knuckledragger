"""Record every `kd.prove` call made while importing the theories, as JSON.

For each call: the goal's symbols and which library lemmas its `by=` used.
For each library lemma (module-level Proofs and definitions): its symbols and
when it was created, so a benchmark only offers lemmas that existed at the call.

    python tools/lemma_suggest/record.py out.json
"""

import itertools
import json
import sys
from collections import Counter
from importlib import import_module
from pathlib import Path

import kdrag as kd
import kdrag.smt as smt
import kdrag.tactics

clock = itertools.count()
created: dict[int, int] = {}  # id(Proof) -> creation tick
_post_init = kd.kernel.Proof.__post_init__


def _record_creation(self):
    _post_init(self)
    created.setdefault(id(self), next(clock))


kd.kernel.Proof.__post_init__ = _record_creation

calls = []
_prove = kdrag.tactics.prove


def _record_prove(thm, *args, by=None, **kwargs):
    pf = _prove(thm, *args, by=by, **kwargs)  # only successful calls are recorded
    if by is None:
        by = []
    elif isinstance(by, kd.Proof):
        by = [by]
    calls.append((next(clock), thm, list(by), caller_module()))
    return pf


def caller_module() -> str:
    f = sys._getframe(2)
    while f is not None:
        name = f.f_globals.get("__name__", "")
        if name.startswith("kdrag.theories"):
            return name
        f = f.f_back
    return "?"


kd.prove = kdrag.tactics.prove = _record_prove


def symbols(e: smt.ExprRef) -> Counter:
    """Function symbols in `e`: uninterpreted names plus `op:` for built-ins."""
    out: Counter = Counter()
    seen = set()
    todo = [e]
    while todo:
        t = todo.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if smt.is_quantifier(t):
            for i in range(t.num_vars()):
                out["sort:" + str(t.var_sort(i))] += 1
            todo.append(t.body())
        elif smt.is_app(t):
            d = t.decl()
            if d.kind() == smt.Z3_OP_UNINTERPRETED:
                if "!" not in d.name():  # skip fresh variables like x!7
                    out[d.name()] += 1
            else:
                out["op:" + d.name()] += 1
            todo.extend(t.children())
    return out


def main(path: str):
    modules = sorted(
        ".".join(("kdrag", "theories", *p.with_suffix("").parts)).removesuffix(
            ".__init__"
        )
        for p in (
            q.relative_to(Path(kd.__file__).parent / "theories")
            for q in (Path(kd.__file__).parent / "theories").rglob("*.py")
        )
    )
    for m in modules:
        try:
            import_module(m)
        except Exception as e:  # noqa: BLE001
            print(f"skip {m}: {type(e).__name__}", file=sys.stderr)

    # Library lemmas: module-level Proofs and definitional axioms, keyed by thm id.
    pool: dict[int, dict] = {}

    def add(pf: kd.Proof, name: str, kind: str):
        key = pf.thm.get_id()
        if key in pool or id(pf) not in created:
            return
        pool[key] = {
            "name": name,
            "kind": kind,
            "tick": created[id(pf)],
            "symbols": symbols(pf.thm),
        }

    for m in modules:
        mod = sys.modules.get(m)
        for n, v in (vars(mod) if mod else {}).items():
            if isinstance(v, kd.Proof) and not n.startswith("_"):
                add(v, f"{m}.{n}", "lemma")
    for decl, unfold in kd.kernel.defns.items():
        add(unfold.ax, f"defn:{decl.name()}", "defn")

    def roots(pf: kd.Proof, depth=4) -> set[str]:
        """Library lemmas a `by=` entry came from, following instantiation."""
        if pf.thm.get_id() in pool:
            return {pool[pf.thm.get_id()]["name"]}
        if depth == 0:
            return set()
        return set().union(
            *(roots(r, depth - 1) for r in pf.reason if isinstance(r, kd.Proof))
        )

    out_calls = []
    for tick, thm, by, module in calls:
        targets = sorted(set().union(*(roots(p) for p in by))) if by else []
        out_calls.append(
            {
                "tick": tick,
                "module": module,
                "symbols": symbols(thm),
                "n_by": len(by),
                "targets": targets,
            }
        )
    json.dump(
        {"lemmas": list(pool.values()), "calls": out_calls}, open(path, "w"), indent=0
    )
    with_targets = sum(1 for c in out_calls if c["targets"])
    print(
        f"{len(pool)} library lemmas, {len(out_calls)} prove calls, "
        f"{with_targets} with library lemmas in by="
    )


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "lemma_calls.json")
