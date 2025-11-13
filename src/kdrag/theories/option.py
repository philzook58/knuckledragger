"""
Algebraic data type for optional values

"""

import kdrag.smt as smt
import kdrag as kd


OptionSort = kd.OptionSort


def is_option(x: smt.DatatypeRef) -> bool:
    """
    Check if a value is an Option
    >>> is_option(kd.Some(42))
    True
    >>> is_option(42)
    False
    """
    return isinstance(x, smt.DatatypeRef) and x.sort().name().startswith("Option_")


# This should also perhaps be a SortDispatch
def get(x: smt.DatatypeRef, default: smt.ExprRef) -> smt.ExprRef:
    """
    Get the value of an Option, or a default value if it is None_
    >>> get(kd.Some(42), 0)
    If(is(Some, Some(42)), val(Some(42)), 0)
    """
    default = smt._py2expr(default)
    if not is_option(x):
        raise ValueError(f"{x} is not an Option datatype. {x.sort()}")
    elif x.val.sort() != default.sort():
        raise ValueError(
            f"default sort {default.sort()} does not match option sort {x.val.sort()}"
        )
    return smt.If(x.is_Some, x.val, default)


def None_(T: smt.SortRef) -> smt.DatatypeRef:
    """
    Helper to create Option None_ values
    >>> None_(smt.IntSort())
    None_
    """
    return OptionSort(T).None_


Some = kd.Some
