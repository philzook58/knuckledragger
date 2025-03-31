import kdrag.smt as smt
import kdrag as kd
import subprocess


def of_sort(s: smt.SortRef) -> str:
    """
    Convert a sort to a Lean type.

    >>> of_sort(smt.BoolSort())
    'Bool'
    >>> of_sort(smt.BitVecSort(8))
    '(BitVec 8)'
    >>> of_sort(smt.ArraySort(smt.BitVecSort(8), smt.BitVecSort(16)))
    '((BitVec 8) -> (BitVec 16))'
    """
    if s == smt.BoolSort():
        return "Bool"
    elif isinstance(s, smt.BitVecSortRef):
        return f"(BitVec {s.size()})"
    elif s == smt.IntSort():
        return "Int"
    elif s == smt.StringSort():
        return "String"
    elif isinstance(s, smt.SeqSortRef):
        return f"(Array {of_sort(s.basis())})"
    elif isinstance(s, smt.ArraySortRef):
        # TODO: multi arity
        return f"({of_sort(s.domain())} -> {of_sort(s.range())})"
    else:
        return s.name()
        # raise NotImplementedError(f"Cannot convert {s} to Lean type")


# datatype definitions


def of_expr(e: smt.ExprRef):
    """

    >>> x,y,z = smt.Ints("x y z")
    >>> of_expr(x)
    'x'
    >>> of_expr(x + y + z)
    '((x + y) + z)'
    >>> of_expr(smt.If(x == x, y, z))
    '(if (x = x) then y else z)'
    """
    if isinstance(e, smt.QuantifierRef):
        if e.is_forall():
            vs, body = kd.utils.open_binder_unhygienic(e)
            return f"∀ {' '.join(v.decl().name() for v in vs)}, {of_expr(body)}"
        elif e.is_exists():
            vs, body = kd.utils.open_binder_unhygienic(e)
            return f"∃ {' '.join(v.decl().name() for v in vs)}, {of_expr(body)}"
        elif e.is_lambda():
            vs, body = kd.utils.open_binder_unhygienic(e)
            return f"λ {' '.join(v.decl().name() for v in vs)}, {of_expr(body)}"
        else:
            raise NotImplementedError(
                "Cannot convert unknown quantifier to Lean expression."
            )
    if isinstance(e, smt.IntNumRef):
        return str(e.as_long())
    elif isinstance(e, smt.BitVecNumRef):
        return f"{e.as_long()}#{e.size()}"
    elif smt.is_app(e):
        decl = e.decl()
        name = decl.name()
        args = [of_expr(arg) for arg in e.children()]
        if smt.is_select(e):
            assert len(args) == 2
            return f"({args[0]} {args[1]})"
        # special case store? fun k -> if k = v then d else a k
        elif smt.is_if(e):
            return f"(if {args[0]} then {args[1]} else {args[2]})"
        elif len(args) == 0:
            return name
        elif not name[0].isalpha() and len(args) == 2:
            return f"({args[0]} {name} {args[1]})"
        else:
            return f"({decl.name()} {' '.join(args)})"
    else:
        raise NotImplementedError(f"Cannot convert {e} to Lean expression. ", e)


def run_lean(filename: str):
    return subprocess.run(["lean", filename], check=True, capture_output=True)
