from dataclasses import dataclass

import kdrag as kd
import kdrag.smt as smt
import kdrag.notation as nt
import kdrag.tactics as tactics


@dataclass(frozen=True)
class Infix:
    symbol: str
    precedence: int


@dataclass(frozen=True)
class Prefix:
    symbol: str
    precedence: int


infix: dict[smt.FuncDeclRef, Infix] = {}
prefix: dict[smt.FuncDeclRef, Prefix] = {}
_notation_infix_keys: set[smt.FuncDeclRef] = set()
_notation_prefix_keys: set[smt.FuncDeclRef] = set()

PREC_QUANT = 10
PREC_IMPLIES = 20
PREC_OR = 30
PREC_AND = 40
PREC_CMP = 50
PREC_BV_OR = 52
PREC_BV_XOR = 54
PREC_BV_AND = 56
PREC_ADD = 60
PREC_CONCAT = 65
PREC_MUL = 70
PREC_UNARY = 80
PREC_SELECT = 90
PREC_STORE = 90
PREC_EXTRACT = 90
PREC_ATOM = 100
CONCAT_SYMBOL = "\\mathbin{+\\!+}"

_NOTATION_INFIXES = (
    (nt.add, "+", PREC_ADD),
    (nt.radd, "+", PREC_ADD),
    (nt.sub, "-", PREC_ADD),
    (nt.mul, "\\cdot", PREC_MUL),
    (nt.rmul, "\\cdot", PREC_MUL),
    (nt.matmul, "@", PREC_MUL),
    (nt.div, "/", PREC_MUL),
    (nt.and_, "\\wedge", PREC_AND),
    (nt.or_, "\\vee", PREC_OR),
    (nt.lt, "<", PREC_CMP),
    (nt.le, "\\leq", PREC_CMP),
    (nt.ge, "\\geq", PREC_CMP),
    (nt.gt, ">", PREC_CMP),
    (nt.eq, "=", PREC_CMP),
    (nt.ne, "\\neq", PREC_CMP),
)

_NOTATION_PREFIXES = (
    (nt.neg, "-", PREC_UNARY),
    (nt.invert, "\\neg", PREC_UNARY),
)

_BV_INFIXES = {
    smt.Z3_OP_BADD: ("+", PREC_ADD),
    smt.Z3_OP_BSUB: ("-", PREC_ADD),
    smt.Z3_OP_BMUL: ("*", PREC_MUL),
    smt.Z3_OP_BAND: ("\\mathbin{\\&}", PREC_BV_AND),
    smt.Z3_OP_BOR: ("\\mid", PREC_BV_OR),
    smt.Z3_OP_BXOR: ("\\oplus", PREC_BV_XOR),
    smt.Z3_OP_BNAND: ("\\barwedge", PREC_BV_AND),
    smt.Z3_OP_BNOR: ("\\downarrow", PREC_BV_OR),
    smt.Z3_OP_BXNOR: ("\\odot", PREC_BV_XOR),
    smt.Z3_OP_BSHL: ("\\ll", PREC_MUL),
    smt.Z3_OP_BLSHR: ("\\gg_u", PREC_MUL),
    smt.Z3_OP_BASHR: ("\\gg_s", PREC_MUL),
    smt.Z3_OP_BUDIV: ("/_u", PREC_MUL),
    smt.Z3_OP_BSDIV: ("/_s", PREC_MUL),
    smt.Z3_OP_BUREM: ("\\bmod_u", PREC_MUL),
    smt.Z3_OP_BSREM: ("\\operatorname{srem}", PREC_MUL),
    smt.Z3_OP_BSMOD: ("\\bmod_s", PREC_MUL),
}

_BV_CMPS = {
    smt.Z3_OP_ULT: "<_u",
    smt.Z3_OP_ULEQ: "\\leq_u",
    smt.Z3_OP_UGT: ">_u",
    smt.Z3_OP_UGEQ: "\\geq_u",
    smt.Z3_OP_SLT: "<_s",
    smt.Z3_OP_SLEQ: "\\leq_s",
    smt.Z3_OP_SGT: ">_s",
    smt.Z3_OP_SGEQ: "\\geq_s",
}


def update_notation() -> None:
    r"""
    Refresh notation from registered `kdrag.notation` operators.

    Only unary and binary `FuncDeclRef` methods are added. Call this after
    importing a theory that registers new notation-backed function declarations.

    >>> from kdrag.theories import real
    >>> update_notation()
    >>> f, g = smt.Consts("f g", real.RFun)
    >>> to_latex(f + g)
    '\\text{f} + \\text{g}'
    >>> from kdrag.theories.real import vec2
    >>> update_notation()
    >>> u = smt.Const("u", vec2.Vec2)
    >>> to_latex(-u)
    '-\\text{u}'
    """
    for key in _notation_infix_keys:
        infix.pop(key, None)
    _notation_infix_keys.clear()
    for key in _notation_prefix_keys:
        prefix.pop(key, None)
    _notation_prefix_keys.clear()

    for dispatch, symbol, precedence in _NOTATION_INFIXES:
        for op in dispatch.methods.values():
            if isinstance(op, smt.FuncDeclRef) and op.arity() == 2:
                infix[op] = Infix(symbol, precedence)
                _notation_infix_keys.add(op)
    for dispatch, symbol, precedence in _NOTATION_PREFIXES:
        for op in dispatch.methods.values():
            if isinstance(op, smt.FuncDeclRef) and op.arity() == 1:
                prefix[op] = Prefix(symbol, precedence)
                _notation_prefix_keys.add(op)


update_notation()


def _wrap(text: str, node_prec: int, outer_prec: int) -> str:
    if node_prec < outer_prec:
        return f"({text})"
    return text


def _is_atomic(expr: smt.ExprRef) -> bool:
    return (
        smt.is_true(expr)
        or smt.is_false(expr)
        or smt.is_int_value(expr)
        or smt.is_const(expr)
    )


def _group_formula(expr: smt.ExprRef) -> str:
    text = to_latex(expr, 0)
    if _is_atomic(expr):
        return text
    return f"({text})"


def _to_latex_bv_value(expr: smt.BitVecNumRef) -> str:
    width = expr.size()
    hex_width = (width + 3) // 4
    return f"\\texttt{{0x{expr.as_long():0{hex_width}x}}}"


def _to_latex_real_value(expr: smt.RatNumRef) -> str:
    frac = expr.as_fraction()
    if frac.denominator == 1:
        return str(frac.numerator)
    if frac.numerator < 0:
        return f"-\\frac{{{-frac.numerator}}}{{{frac.denominator}}}"
    return f"\\frac{{{frac.numerator}}}{{{frac.denominator}}}"


def _to_latex_string_value(expr: smt.SeqRef) -> str:
    return _to_latex_text(f'"{expr.as_string()}"')


def _to_latex_fp_value(expr: smt.FPNumRef) -> str:
    text = str(expr)
    if text == "NaN":
        return "\\mathsf{NaN}"
    if text == "+oo":
        return "+\\infty"
    if text == "-oo":
        return "-\\infty"
    return text


def _to_latex_fprm_value(expr: smt.FPRMRef) -> str:
    text = str(expr)
    if text.endswith("()"):
        text = text[:-2]
    return f"\\mathsf{{{text}}}"


def _is_empty_set(expr: smt.ExprRef) -> bool:
    return (
        isinstance(expr, smt.ArrayRef)
        and isinstance(expr.sort(), smt.ArraySortRef)
        and expr.sort().range() == smt.BoolSort()
        and smt.is_const_array(expr)
        and len(expr.children()) == 1
        and smt.is_false(expr.children()[0])
    )


def _is_seq_unit(expr: smt.ExprRef) -> bool:
    return smt.is_app(expr) and expr.decl().kind() == smt.Z3_OP_SEQ_UNIT


def _to_latex_ite(expr: smt.ExprRef) -> str:
    cases, default = kd.utils.ite_to_cases(expr)
    rows = [
        f"{to_latex(value, 0)} & \\text{{if }} {to_latex(cond, 0)}"
        for cond, value in cases
    ]
    rows.append(f"{to_latex(default, 0)} & \\text{{otherwise}}")
    return "\\begin{cases} " + " \\\\ ".join(rows) + " \\end{cases}"


def _to_latex_text(text: str) -> str:
    escaped = (
        text.replace("\\", "\\textbackslash{}")
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("_", "\\_")
        .replace("%", "\\%")
        .replace("&", "\\&")
        .replace("#", "\\#")
        .replace("$", "\\$")
    )
    return f"\\text{{{escaped}}}"


def _to_latex_decl_subscript(text: str) -> str:
    if text.isdigit():
        return text
    return _to_latex_text(text)


def _to_latex_decl_name(name: object) -> str:
    text = str(name)
    prefix, sep, leaf = text.rpartition(".")
    base, *bang_subscripts = leaf.split("!")
    subscripts = bang_subscripts
    if sep:
        subscripts.append(prefix)
    base_text = _to_latex_text(base)
    if not subscripts:
        return base_text
    subscript_text = ", ".join(_to_latex_decl_subscript(s) for s in subscripts)
    return f"{base_text}_{{{subscript_text}}}"


def _to_latex_bv_infix(children: list[smt.ExprRef], symbol: str, op_prec: int) -> str:
    assert len(children) == 2
    lhs, rhs = children
    return f"{to_latex(lhs, op_prec)} {symbol} {to_latex(rhs, op_prec + 1)}"


def _to_latex_typed_var(var: smt.ExprRef) -> str:
    return f"{to_latex_expr(var)} : {to_latex_sort(var.sort())}"


def to_latex_sort(sort: smt.SortRef) -> str:
    r"""
    >>> to_latex_sort(smt.BoolSort())
    '\\mathsf{Bool}'
    >>> to_latex_sort(smt.IntSort())
    '\\mathsf{Int}'
    >>> to_latex_sort(smt.RealSort())
    '\\mathsf{Real}'
    >>> to_latex_sort(smt.BitVecSort(8))
    '\\mathsf{BV}_{8}'
    >>> to_latex_sort(smt.SeqSort(smt.IntSort()))
    '\\mathsf{Seq}(\\mathsf{Int})'
    >>> to_latex_sort(smt.ArraySort(smt.IntSort(), smt.BoolSort()))
    '\\mathsf{Int} \\to \\mathsf{Bool}'
    >>> to_latex_sort(smt.ArraySort(smt.BitVecSort(8), smt.ArraySort(smt.IntSort(), smt.BoolSort())))
    '\\mathsf{BV}_{8} \\to (\\mathsf{Int} \\to \\mathsf{Bool})'
    >>> to_latex_sort(kd.TupleSort(smt.IntSort(), smt.BoolSort()))
    '\\langle \\mathsf{Int}, \\mathsf{Bool} \\rangle'
    """
    if sort == smt.BoolSort():
        return "\\mathsf{Bool}"
    if sort == smt.IntSort():
        return "\\mathsf{Int}"
    if sort == smt.RealSort():
        return "\\mathsf{Real}"
    if sort == smt.StringSort():
        return "\\mathsf{String}"
    if isinstance(sort, smt.BitVecSortRef):
        return f"\\mathsf{{BV}}_{{{sort.size()}}}"
    if isinstance(sort, smt.SeqSortRef):
        return f"\\mathsf{{Seq}}({to_latex_sort(sort.basis())})"
    if isinstance(sort, smt.ArraySortRef):
        dom = to_latex_sort(sort.domain())
        rng_sort = sort.range()
        rng = to_latex_sort(rng_sort)
        if isinstance(rng_sort, smt.ArraySortRef):
            rng = f"({rng})"
        return f"{dom} \\to {rng}"
    if isinstance(sort, smt.DatatypeSortRef) and kd.is_tuple_sort(sort):
        fields = ", ".join(
            to_latex_sort(sort.accessor(0, i).range())
            for i in range(sort.constructor(0).arity())
        )
        return f"\\langle {fields} \\rangle"
    if isinstance(sort, smt.FPSortRef):
        return f"\\mathsf{{FP}}({sort.ebits()}, {sort.sbits()})"
    return f"\\mathsf{{{sort.name()}}}"


def to_latex_expr(expr: smt.ExprRef, prec: int = 0) -> str:
    r"""
    >>> x, y = smt.Ints("x y")
    >>> to_latex(x)
    '\\text{x}'
    >>> to_latex(smt.IntVal(42))
    '42'
    >>> to_latex(smt.BoolVal(True))
    '\\top'
    >>> to_latex(smt.BoolVal(False))
    '\\bot'
    >>> to_latex(smt.RealVal(2))
    '2'
    >>> to_latex(smt.RealVal("3/2"))
    '\\frac{3}{2}'
    >>> to_latex(smt.RealVal("-3/2"))
    '-\\frac{3}{2}'
    >>> to_latex(smt.StringVal("a_b"))
    '\\text{"a\\_b"}'
    >>> to_latex(smt.FPVal(1.5, smt.Float32()))
    '1.5'
    >>> to_latex(smt.FPVal(float("inf"), smt.Float32()))
    '+\\infty'
    >>> to_latex(smt.RNE())
    '\\mathsf{RNE}'
    >>> to_latex(smt.CharVal(65))
    '\\operatorname{char}(65)'
    >>> to_latex((x + 1) * y)
    '(\\text{x} + 1) \\cdot \\text{y}'
    >>> to_latex(x - (y + 1))
    '\\text{x} - (\\text{y} + 1)'
    >>> to_latex(-x)
    '-\\text{x}'
    >>> to_latex(-(x + y))
    '-(\\text{x} + \\text{y})'
    >>> to_latex(x / (y + 1))
    '\\text{x} / (\\text{y} + 1)'
    >>> to_latex(x % (y + 1))
    '\\text{x} \\bmod (\\text{y} + 1)'
    >>> to_latex(smt.If(x < y, x + 1, y + 1))
    '\\begin{cases} \\text{x} + 1 & \\text{if } \\text{x} < \\text{y} \\\\ \\text{y} + 1 & \\text{otherwise} \\end{cases}'
    >>> to_latex(smt.If(x < 0, -x, smt.If(x == 0, 0, x + 1)))
    '\\begin{cases} -\\text{x} & \\text{if } \\text{x} < 0 \\\\ 0 & \\text{if } \\text{x} = 0 \\\\ \\text{x} + 1 & \\text{otherwise} \\end{cases}'
    >>> to_latex(smt.And(x < y, y <= x + 1))
    '(\\text{x} < \\text{y}) \\wedge (\\text{y} \\leq \\text{x} + 1)'
    >>> to_latex(smt.And(x > y, y >= x + 1))
    '(\\text{x} > \\text{y}) \\wedge (\\text{y} \\geq \\text{x} + 1)'
    >>> to_latex(smt.Or(x < y, y < x))
    '(\\text{x} < \\text{y}) \\vee (\\text{y} < \\text{x})'
    >>> to_latex(smt.Not(x < y))
    '\\neg (\\text{x} < \\text{y})'
    >>> to_latex(smt.Implies(smt.And(x < y, y < 10), x < 9))
    '((\\text{x} < \\text{y}) \\wedge (\\text{y} < 10)) \\rightarrow (\\text{x} < 9)'
    >>> to_latex(smt.ForAll([x, y], smt.Implies(x < y, x + 1 <= y)))
    '\\forall \\text{x}, \\text{y}. (\\text{x} < \\text{y}) \\rightarrow (\\text{x} + 1 \\leq \\text{y})'
    >>> to_latex(smt.Lambda([x], x + 1))
    '\\lambda \\text{x}. \\text{x} + 1'
    >>> to_latex(smt.Lambda([x, y], x < y))
    '\\lambda \\text{x}, \\text{y}. \\text{x} < \\text{y}'
    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort())
    >>> to_latex(f(x + 1))
    '\\text{f}(\\text{x} + 1)'
    >>> namespaced = smt.Const("Foo.Bar.biz", smt.IntSort())
    >>> to_latex(namespaced)
    '\\text{biz}_{\\text{Foo.Bar}}'
    >>> to_latex(smt.Const("x!127", smt.IntSort()))
    '\\text{x}_{127}'
    >>> to_latex(smt.Const("Foo.Bar.x!127", smt.IntSort()))
    '\\text{x}_{127, \\text{Foo.Bar}}'
    >>> g = smt.Function("Foo.Bar.g", smt.IntSort(), smt.IntSort())
    >>> to_latex(g(x))
    '\\text{g}_{\\text{Foo.Bar}}(\\text{x})'
    >>> to_latex(kd.prove(x < x + 1))
    '\\vdash \\text{x} < \\text{x} + 1'
    >>> a, b = smt.BitVecs("a b", 8)
    >>> to_latex(smt.BitVecVal(0xA, 8))
    '\\texttt{0x0a}'
    >>> to_latex(smt.BitVecVal(0xBEEF, 16))
    '\\texttt{0xbeef}'
    >>> to_latex(smt.Concat(a, b))
    '\\text{a} \\mathbin{+\\!+} \\text{b}'
    >>> to_latex(a + b)
    '\\text{a} + \\text{b}'
    >>> to_latex(a - b)
    '\\text{a} - \\text{b}'
    >>> to_latex(a * b)
    '\\text{a} * \\text{b}'
    >>> to_latex(smt.Extract(7, 4, a))
    '\\text{a}[7:4]'
    >>> to_latex(smt.Extract(3, 3, a))
    '\\text{a}[3]'
    >>> to_latex(smt.Extract(11, 4, smt.Concat(a, b)))
    '(\\text{a} \\mathbin{+\\!+} \\text{b})[11:4]'
    >>> to_latex(a & b)
    '\\text{a} \\mathbin{\\&} \\text{b}'
    >>> to_latex(a | b)
    '\\text{a} \\mid \\text{b}'
    >>> to_latex(a ^ b)
    '\\text{a} \\oplus \\text{b}'
    >>> to_latex(~a)
    '\\sim \\text{a}'
    >>> to_latex(a << 2)
    '\\text{a} \\ll \\texttt{0x02}'
    >>> to_latex(smt.LShR(a, 2))
    '\\text{a} \\gg_u \\texttt{0x02}'
    >>> to_latex(a >> 2)
    '\\text{a} \\gg_s \\texttt{0x02}'
    >>> to_latex(smt.ULT(a, b))
    '\\text{a} <_u \\text{b}'
    >>> to_latex(a < b)
    '\\text{a} <_s \\text{b}'
    >>> to_latex(smt.ZeroExt(4, a))
    '\\operatorname{zext}_{4}(\\text{a})'
    >>> to_latex(smt.SignExt(4, a))
    '\\operatorname{sext}_{4}(\\text{a})'
    >>> to_latex(smt.RotateLeft(a, 3))
    '\\operatorname{rotl}(\\text{a}, \\texttt{0x03})'
    >>> to_latex(smt.RotateRight(a, 3))
    '\\operatorname{rotr}(\\text{a}, \\texttt{0x03})'
    >>> A = smt.Array("A", smt.IntSort(), smt.BitVecSort(8))
    >>> to_latex(A[x + 1])
    '\\text{A}[\\text{x} + 1]'
    >>> to_latex(smt.Store(A, x, a))
    '\\text{A}[\\text{x} := \\text{a}]'
    >>> to_latex(smt.Store(smt.Store(A, x, a), y, b))
    '\\text{A}[\\text{x} := \\text{a}][\\text{y} := \\text{b}]'
    >>> to_latex(smt.EmptySet(smt.IntSort()))
    '\\emptyset'
    >>> to_latex(smt.Unit(x))
    '[\\text{x}]'
    >>> to_latex(smt.Unit(x + 1))
    '[\\text{x} + 1]'
    >>> to_latex(smt.Concat(smt.Unit(x), smt.Unit(y)))
    '[\\text{x}] \\mathbin{+\\!+} [\\text{y}]'
    """
    if isinstance(expr, smt.QuantifierRef):
        vs, body = kd.utils.open_binder_unhygienic(expr)
        vs_str = ", ".join(to_latex(v, PREC_ATOM) for v in vs)
        body_str = to_latex(body, PREC_QUANT)
        if expr.is_lambda():
            return _wrap(f"\\lambda {vs_str}. {body_str}", PREC_QUANT, prec)
        if expr.is_forall():
            return _wrap(f"\\forall {vs_str}. {body_str}", PREC_QUANT, prec)
        return _wrap(f"\\exists {vs_str}. {body_str}", PREC_QUANT, prec)
    if smt.is_true(expr):
        return "\\top"
    if smt.is_false(expr):
        return "\\bot"
    if smt.is_int_value(expr):
        assert isinstance(expr, smt.IntNumRef)
        return str(expr.as_long())
    if smt.is_rational_value(expr):
        assert isinstance(expr, smt.RatNumRef)
        return _to_latex_real_value(expr)
    if smt.is_bv_value(expr):
        assert isinstance(expr, smt.BitVecNumRef)
        return _to_latex_bv_value(expr)
    if smt.is_string_value(expr):
        assert isinstance(expr, smt.SeqRef)
        return _to_latex_string_value(expr)
    if smt.is_fp_value(expr):
        assert isinstance(expr, smt.FPNumRef)
        return _to_latex_fp_value(expr)
    if smt.is_fprm_value(expr):
        assert isinstance(expr, smt.FPRMRef)
        return _to_latex_fprm_value(expr)
    if smt.is_app(expr) and expr.decl().kind() == smt.Z3_OP_CHAR_CONST:
        return f"\\operatorname{{char}}({expr})"
    if _is_empty_set(expr):
        return "\\emptyset"
    if smt.is_const(expr):
        return _to_latex_decl_name(expr.decl().name())
    if not smt.is_app(expr):
        raise TypeError(f"Unexpected expression type in to_latex_expr: {expr!r}")

    children = expr.children()
    cmp_child_strs = [to_latex(child, PREC_CMP) for child in children]

    if smt.is_not(expr):
        text = f"\\neg {_group_formula(children[0])}"
        return _wrap(text, PREC_CMP, prec)
    if smt.is_if(expr):
        return _wrap(_to_latex_ite(expr), PREC_QUANT, prec)
    if smt.is_add(expr):
        text = " + ".join(to_latex(child, PREC_ADD) for child in children)
        return _wrap(text, PREC_ADD, prec)
    if smt.is_sub(expr):
        lhs, rhs = children
        text = f"{to_latex(lhs, PREC_ADD)} - {to_latex(rhs, PREC_ADD + 1)}"
        return _wrap(text, PREC_ADD, prec)
    if smt.is_mul(expr):
        text = " \\cdot ".join(to_latex(child, PREC_MUL) for child in children)
        return _wrap(text, PREC_MUL, prec)
    if smt.is_div(expr) or expr.decl().kind() in (smt.Z3_OP_DIV, smt.Z3_OP_IDIV):
        lhs, rhs = children
        text = f"{to_latex(lhs, PREC_MUL)} / {to_latex(rhs, PREC_MUL + 1)}"
        return _wrap(text, PREC_MUL, prec)
    if smt.is_mod(expr):
        lhs, rhs = children
        text = f"{to_latex(lhs, PREC_MUL)} \\bmod {to_latex(rhs, PREC_MUL + 1)}"
        return _wrap(text, PREC_MUL, prec)
    if smt.is_neg(expr):
        text = f"-{to_latex(children[0], PREC_UNARY)}"
        return _wrap(text, PREC_UNARY, prec)
    kind = expr.decl().kind()
    if kind in _BV_INFIXES:
        symbol, op_prec = _BV_INFIXES[kind]
        text = _to_latex_bv_infix(children, symbol, op_prec)
        return _wrap(text, op_prec, prec)
    if kind == smt.Z3_OP_BNOT:
        text = f"\\sim {to_latex(children[0], PREC_UNARY)}"
        return _wrap(text, PREC_UNARY, prec)
    if kind == smt.Z3_OP_ZERO_EXT:
        (amount,) = expr.decl().params()
        text = f"\\operatorname{{zext}}_{{{amount}}}({to_latex(children[0], 0)})"
        return _wrap(text, PREC_ATOM, prec)
    if kind == smt.Z3_OP_SIGN_EXT:
        (amount,) = expr.decl().params()
        text = f"\\operatorname{{sext}}_{{{amount}}}({to_latex(children[0], 0)})"
        return _wrap(text, PREC_ATOM, prec)
    if kind in (smt.Z3_OP_ROTATE_LEFT, smt.Z3_OP_ROTATE_RIGHT):
        (amount,) = expr.decl().params()
        name = "rotl" if kind == smt.Z3_OP_ROTATE_LEFT else "rotr"
        text = f"\\operatorname{{{name}}}({to_latex(children[0], 0)}, {amount})"
        return _wrap(text, PREC_ATOM, prec)
    if kind in (smt.Z3_OP_EXT_ROTATE_LEFT, smt.Z3_OP_EXT_ROTATE_RIGHT):
        name = "rotl" if kind == smt.Z3_OP_EXT_ROTATE_LEFT else "rotr"
        text = (
            f"\\operatorname{{{name}}}"
            f"({to_latex(children[0], 0)}, {to_latex(children[1], 0)})"
        )
        return _wrap(text, PREC_ATOM, prec)
    if _is_seq_unit(expr):
        text = f"[{to_latex(children[0], 0)}]"
        return _wrap(text, PREC_ATOM, prec)
    if kind in (smt.Z3_OP_CONCAT, smt.Z3_OP_SEQ_CONCAT):
        text = f" {CONCAT_SYMBOL} ".join(
            to_latex(child, PREC_CONCAT) for child in children
        )
        return _wrap(text, PREC_CONCAT, prec)
    if expr.decl().kind() == smt.Z3_OP_EXTRACT and smt.is_bv(expr):
        high, low = expr.decl().params()
        idx = str(high) if high == low else f"{high}:{low}"
        text = f"{to_latex(children[0], PREC_EXTRACT)}[{idx}]"
        return _wrap(text, PREC_EXTRACT, prec)
    if smt.is_store(expr):
        array, *addrs, value = children
        addr_text = ", ".join(to_latex(addr, 0) for addr in addrs)
        text = f"{to_latex(array, PREC_STORE)}" f"[{addr_text} := {to_latex(value, 0)}]"
        return _wrap(text, PREC_STORE, prec)
    if smt.is_select(expr):
        array, *addrs = children
        addr_text = ", ".join(to_latex(addr, 0) for addr in addrs)
        text = f"{to_latex(array, PREC_SELECT)}[{addr_text}]"
        return _wrap(text, PREC_SELECT, prec)
    if kind in _BV_CMPS:
        text = f"{to_latex(children[0], PREC_CMP)} {_BV_CMPS[kind]} {to_latex(children[1], PREC_CMP + 1)}"
        return _wrap(text, PREC_CMP, prec)
    if smt.is_eq(expr):
        text = " = ".join(cmp_child_strs)
        return _wrap(text, PREC_CMP, prec)
    if smt.is_le(expr):
        text = " \\leq ".join(cmp_child_strs)
        return _wrap(text, PREC_CMP, prec)
    if smt.is_ge(expr):
        text = " \\geq ".join(cmp_child_strs)
        return _wrap(text, PREC_CMP, prec)
    if smt.is_lt(expr):
        text = " < ".join(cmp_child_strs)
        return _wrap(text, PREC_CMP, prec)
    if smt.is_gt(expr):
        text = " > ".join(cmp_child_strs)
        return _wrap(text, PREC_CMP, prec)
    if smt.is_and(expr):
        text = " \\wedge ".join(_group_formula(child) for child in children)
        return _wrap(text, PREC_AND, prec)
    if smt.is_or(expr):
        text = " \\vee ".join(_group_formula(child) for child in children)
        return _wrap(text, PREC_OR, prec)
    if smt.is_implies(expr):
        text = " \\rightarrow ".join(_group_formula(child) for child in children)
        return _wrap(text, PREC_IMPLIES, prec)
    if smt.is_distinct(expr):
        text = " \\neq ".join(cmp_child_strs)
        return _wrap(text, PREC_CMP, prec)

    decl = expr.decl()
    if decl in infix:
        op = infix[decl]
        assert len(children) == 2
        text = (
            f"{to_latex(children[0], op.precedence)} "
            f"{op.symbol} "
            f"{to_latex(children[1], op.precedence)}"
        )
        return _wrap(text, op.precedence, prec)
    if decl in prefix:
        op = prefix[decl]
        assert len(children) == 1
        text = f"{op.symbol}{to_latex(children[0], op.precedence)}"
        return _wrap(text, op.precedence, prec)
    return f"{_to_latex_decl_name(decl.name())}({', '.join(to_latex(child, 0) for child in children)})"


def to_latex_proof(proof: kd.Proof, prec: int = 0) -> str:
    return f"\\vdash {to_latex_expr(proof.thm, prec)}"


def to_latex_goal(goal: tactics.Goal) -> str:
    r"""
    >>> x = smt.Int("x")
    >>> g = tactics.Goal(sig=[x], ctx=[x > 0, x < 10], goal=x == 5)
    >>> to_latex_goal(g)
    '\\begin{array}{ll} \\text{fix} & \\text{x} : \\mathsf{Int} \\\\ h_{0} & \\text{x} > 0 \\\\ h_{1} & \\text{x} < 10 \\\\ \\hline \\vdash & \\text{x} = 5 \\end{array}'
    >>> to_latex_goal(tactics.Goal.empty())
    '\\text{Nothing to do!}'
    """
    if goal.is_empty():
        return "\\text{Nothing to do!}"

    rows: list[str] = []
    if goal.sig:
        sig = ", ".join(_to_latex_typed_var(var) for var in goal.sig)
        rows.append(f"\\text{{fix}} & {sig}")
    rows.extend(
        f"h_{{{i}}} & {to_latex_expr(hyp)}" for i, hyp in enumerate(goal.ctx)
    )
    rows.append(f"\\hline \\vdash & {to_latex_expr(goal.goal)}")
    return "\\begin{array}{ll} " + " \\\\ ".join(rows) + " \\end{array}"


def to_latex_proof_state(state: tactics.ProofState) -> str:
    return to_latex_goal(state.top_goal())


def to_latex(
    obj: smt.ExprRef | smt.SortRef | kd.Proof | tactics.Goal | tactics.ProofState,
    prec: int = 0,
) -> str:
    r"""
    >>> x = smt.Int("x")
    >>> to_latex(x + 1)
    '\\text{x} + 1'
    >>> to_latex(smt.IntSort())
    '\\mathsf{Int}'
    >>> to_latex(kd.prove(x < x + 1))
    '\\vdash \\text{x} < \\text{x} + 1'
    >>> l = tactics.Lemma(x > 0)
    >>> to_latex(l)
    '\\begin{array}{ll} \\hline \\vdash & \\text{x} > 0 \\end{array}'
    """
    if isinstance(obj, kd.Proof):
        return to_latex_proof(obj, prec)
    if isinstance(obj, tactics.Goal):
        return to_latex_goal(obj)
    if isinstance(obj, tactics.ProofState):
        return to_latex_proof_state(obj)
    if isinstance(obj, smt.SortRef):
        return to_latex_sort(obj)
    if isinstance(obj, smt.ExprRef):
        return to_latex_expr(obj, prec)
    raise TypeError(f"Unexpected object type in to_latex: {obj!r}")
