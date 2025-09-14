import kdrag.smt as smt
import kdrag as kd
import subprocess


def decl_sig(f: smt.FuncDeclRef) -> str:
    """
    Convert a function declaration to a Lean signature.

    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort(), smt.BoolSort())
    >>> decl_sig(f)
    'f : Int -> Int -> Bool'
    """
    typs = [f.domain(n) for n in range(f.arity())] + [f.range()]
    typ = " -> ".join(map(of_sort, typs))
    return f"{f.name()} : {typ}"


def decl_axiom(f: smt.FuncDeclRef) -> str:
    """
    Convert a function declaration to a Lean axiom definition.

    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort(), smt.BoolSort())
    >>> decl_axiom(f)
    'axiom f : Int -> Int -> Bool\\n'
    """
    return f"axiom {decl_sig(f)}\n"


def sort_axiom(s: smt.SortRef) -> str:
    """
    Convert uninterpreted sort to a Lean axiom definition.
    """
    name = s.name()
    assert name not in ["Bool", "Int"]
    return f"""
axiom {name} : Type
axiom {name}_Inhabited : Inhabited {name}
axiom {name}_BEq : BEq {name}
axiom {name}_DecidableEq : DecidableEq {name}

"""


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


def of_datatype(dt: smt.DatatypeSortRef) -> str:
    """
    Convert a datatype to a Lean inductive type definition.

    >>> Nat = smt.Datatype("Nat")
    >>> Nat.declare("Zero")
    >>> Nat.declare("Succ", ("pred", Nat))
    >>> Nat = Nat.create()
    >>> of_datatype(Nat)
    'inductive Nat : Type where\\n| Zero : Nat\\n| Succ : Nat -> Nat\\nderiving BEq, Inhabited, Repr, DecidableEq\\n'
    """
    name = dt.name()
    output = [f"inductive {name} : Type where"]
    for n in range(dt.num_constructors()):
        cons = dt.constructor(n)
        output.append(f"| {decl_sig(cons)}")
    output.append("deriving BEq, Inhabited, Repr, DecidableEq\n")
    return "\n".join(output)


def accessor_def(dt: smt.DatatypeSortRef, n: int, i: int) -> str:
    """
    Make a lean definition that matches accessor, otherwise returns default.
    This might not be a perfect translation of accessor behavior in SMTLIB
    """

    cons = dt.constructor(n)
    acc = dt.accessor(n, i)
    pargs = " ".join(["_" if j != i else "x" for j in range(cons.arity())])
    return f"""
@[grind]
def {decl_sig(acc)}
| .{dt.constructor(n).name()} {pargs} => x 
| _ => default

"""


def of_expr(e: smt.ExprRef):
    """

    >>> x,y,z = smt.Ints("x y z")
    >>> of_expr(x)
    '(x : Int)'
    >>> of_expr(x + y + z)
    '(((x : Int) + (y : Int)) + (z : Int))'
    >>> of_expr(smt.If(x == x, y, z))
    '(if ((x : Int) = (x : Int)) then (y : Int) else (z : Int))'
    """
    if isinstance(e, smt.QuantifierRef):
        vs, body = kd.utils.open_binder_unhygienic(e)
        vs = " ".join([f"({v.decl().name()} : {of_sort(v.sort())})" for v in vs])
        body = of_expr(body)
        if e.is_forall():
            return f"(Classical.propDecidable (∀ {vs}, {body})).decide"
        elif e.is_exists():
            return f"(Classical.propDecidable (∃ {vs}, {body})).decide"
        elif e.is_lambda():
            return f"(λ {vs}, {body})"
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
            return f"({name} : {of_sort(e.sort())})"
        elif name == "distinct":
            assert len(args) == 2
            return f"(Not ({args[0]} = {args[1]}))"
        elif name == "=>":
            assert len(args) == 2
            return f"(not {args[0]} || {args[1]})"
        elif name == "or":
            return f"({' || '.join(args)})"
        elif name == "and":
            return f"({' && '.join(args)})"
        elif name == "bvand":
            return f"({' &&& '.join(args)})"
        elif name == "bvor":
            return f"({' ||| '.join(args)})"
        elif name == "bvadd":
            return f"({' + '.join(args)})"
        elif name == "bvsub":
            return f"({' - '.join(args)})"
        elif name == "bvmul":
            return f"({' * '.join(args)})"
        elif not name[0].isalpha() and len(args) == 2:
            return f"({args[0]} {name} {args[1]})"
        else:
            return f"({decl.name()} {' '.join(args)})"
    else:
        raise NotImplementedError(f"Cannot convert {e} to Lean expression. ", e)


def run_lean(filename: str):
    return subprocess.run(["lean", filename], check=True, capture_output=True)
