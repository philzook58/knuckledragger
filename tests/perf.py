if __name__ == "__main__":
    import kdrag as kd
    import kdrag.config as config
    config.timing = True
    import time
    start_time = time.perf_counter()
    modules = []
    def mark(tag):
        global start_time
        elapsed_time = time.perf_counter() - start_time
        modules.append((elapsed_time, tag))
        start_time = time.perf_counter()
    start_time = time.perf_counter()
    import kdrag.all
    mark("kdrag.all")
    import kdrag.theories.real as R
    mark("real")
    import kdrag.theories.bitvec as bitvec
    mark("bitvec")
    import kdrag.theories.real.complex as complex
    mark("complex")
    import kdrag.theories.algebra.group as group
    mark("group")
    import kdrag.theories.algebra.lattice
    mark("lattice")
    import kdrag.theories.algebra.ordering
    mark("ordering")
    import kdrag.theories.bool as bool_
    mark("bool")
    import kdrag.theories.int
    mark("int")
    import kdrag.theories.real.interval
    mark("interval")
    import kdrag.theories.seq as seq
    mark("seq")
    import kdrag.theories.set
    mark("set")
    import kdrag.theories.fixed
    mark("fixed")
    import kdrag.theories.float
    mark("float")
    import kdrag.theories.real.arb
    mark("arb")
    import kdrag.theories.real.sympy
    mark("sympy")
    import kdrag.theories.nat
    mark("nat")
    import kdrag.theories.real.vec
    mark("vec")
    import kdrag.theories.logic.intuitionistic
    mark("intuitionistic")
    import kdrag.theories.logic.temporal
    mark("temporal")

    print("\n========= Module import times ========\n")
    for (elapsed_time, tag) in sorted(modules, reverse=True):
        print(f"{elapsed_time:.6f} {tag}")

    import itertools
    for tag, group in itertools.groupby(sorted(config.perf_log, key=lambda x: x[0]), key=lambda x: x[0]):
        print("\n=============" + tag + "=============\n")
        for (tag, data, time) in sorted(group, key=lambda x: x[2], reverse=True)[:20]:
            print(f"{time:.6f}: {data}")