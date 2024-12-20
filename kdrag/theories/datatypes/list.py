import kdrag as kd
import functools


@functools.cache
def List(sort):
    dt = kd.Inductive(f"List<{sort.name()}>")
    dt.add_constructor("Nil")
    dt.add_constructor("Cons", ("cons", sort), ("tail", dt))
    return dt.create()
