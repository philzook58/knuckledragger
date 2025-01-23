import kdrag.smt as smt
import kdrag as kd
import typing
import fractions


def sort_of_type(t: type) -> smt.SortRef:
    """
    Give equivalent SMT sort for a given Python type.


    >>> sort_of_type(int)
    Int
    >>> sort_of_type(list[int])
    Seq(Int)
    >>> sort_of_type(dict[str, int])
    Array(String, Int)

    """
    origin = typing.get_origin(t)

    if origin is None:
        if t is int:
            return smt.IntSort()
        elif t is fractions.Fraction:
            return smt.RealSort()
        elif t is bool:
            return smt.BoolSort()
        elif t is float:
            return smt.RealSort()  # Floats correspond to reals in SMT
        elif t is str:
            return smt.StringSort()
        # elif is_subclassof(t, NamedTuple):
        #    # Handle NamedTuple fields as a tuple sort
        #    fields = t._field_types  # Get fields and types from the NamedTuple
        #    return smt.TupleSort(*[sort_of_type(typ) for typ in fields.values()])
        else:
            raise NotImplementedError(f"Type {t} is not supported")
    else:
        # Handle generic types
        args = typing.get_args(t)
        if origin is list:
            if len(args) != 1:
                raise NotImplementedError("List must have exactly one type parameter")
            return smt.SeqSort(sort_of_type(args[0]))  # Lists as sequences
        # elif origin is tuple:
        #    return smt.TupleSort(*[sort_of_type(arg) for arg in args])
        elif origin is dict:
            if len(args) != 2:
                raise NotImplementedError("Dict must have exactly two type parameters")
            return smt.ArraySort(sort_of_type(args[0]), sort_of_type(args[1]))
        # elif origin == Union:
        #    return smt.DatatypeSortRef(*[sort_of_type(arg) for arg in args])
        else:
            raise NotImplementedError(f"Generic type {origin} is not supported")


def type_of_sort(s: smt.SortRef) -> type:
    """
    Give equivalent Python type for a given SMT sort.

    >>> type_of_sort(smt.IntSort())
    <class 'int'>
    >>> type_of_sort(smt.ArraySort(smt.StringSort(), smt.IntSort()))
    dict[str, int]
    >>> type_of_sort(smt.SeqSort(smt.IntSort()))
    list[int]
    """
    if s == smt.IntSort():
        return int
    elif s == smt.RealSort():
        return fractions.Fraction
    elif s == smt.BoolSort():
        return bool
    elif s == smt.StringSort():
        return str
    elif isinstance(s, smt.ArraySortRef):
        return dict[type_of_sort(s.domain()), type_of_sort(s.range())]
    elif isinstance(s, smt.SeqSortRef):
        return list[type_of_sort(s.basis())]
    else:
        raise NotImplementedError(f"Sort {s} is not supported")
