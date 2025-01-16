import functools
import kdrag.smt as smt
import kdrag as kd


@functools.cache
def Option(T: smt.SortRef, admit=False) -> smt.DatatypeSortRef:
    """
    Define an Option type for a given type T
    >>> OInt = Option(smt.IntSort())
    >>> OInt.Some(1)
    Some(1)
    >>> OInt.None_
    None_
    >>> OInt.Some(1).val
    val(Some(1))
    """
    Option = kd.Inductive("Option_" + T.name(), admit=admit)
    Option.declare("None_")
    Option.declare("Some", ("val", T))
    Option = Option.create()
    return Option


def is_option(x: smt.DatatypeRef) -> bool:
    """
    Check if a value is an Option
    >>> is_option(Some(42))
    True
    >>> is_option(42)
    False
    """
    return smt._py2expr(x).sort().name().startswith("Option_")


# This should also perhaps be a SortDispatch
def get(x: smt.DatatypeRef, default: smt.ExprRef) -> smt.ExprRef:
    """
    Get the value of an Option, or a default value if it is None_
    >>> get(Some(42), 0)
    If(is(Some, Some(42)), val(Some(42)), 0)
    """
    if not is_option(x):
        raise ValueError(f"{x} is not an Option datatype. {x.sort()}")
    assert hasattr(x, "is_Some") and hasattr(x, "val")
    if x.val.sort() != default.sort():
        raise ValueError(
            f"default sort {default.sort()} does not match option sort {x.val.sort()}"
        )
    return smt.If(x.is_Some, x.val, default)


# I guess I could make this a SortDispatch for regularity. I just don't see why I'd need to overload in any way but the default
def Some(x: smt.ExprRef) -> smt.DatatypeRef:
    """
    Helper to create Option values
    >>> Some(42)
    Some(42)
    >>> Some(42).sort()
    Option_Int
    """
    x = smt._py2expr(x)
    return Option(x.sort()).Some(x)


def None_(T: smt.SortRef) -> smt.DatatypeRef:
    """
    Helper to create Option None_ values
    >>> None_(smt.IntSort())
    None_
    """
    return Option(T).None_
