"""Compact, width-aware display of SMT expressions and tactic goals."""

from dataclasses import dataclass
import re
from typing import TYPE_CHECKING, Literal, NamedTuple, cast

from kdrag import notation, smt
from kdrag.utils import ite_to_cases

if TYPE_CHECKING:
    from kdrag.tactics import Goal


@dataclass(frozen=True)
class _Break:
    flat: str = " "


@dataclass(frozen=True)
class _Nest:
    doc: "_Doc"


@dataclass(frozen=True)
class _Group:
    doc: "_Doc"


type _Doc = str | tuple[_Doc, ...] | _Break | _Nest | _Group


def _layout(doc: _Doc, width: int) -> str:
    def fits(column: int, pending: list[tuple[int, bool, _Doc]]) -> bool:
        while pending and column <= width:
            indent, flat, part = pending.pop()
            if isinstance(part, str):
                column += len(part)
            elif isinstance(part, _Break):
                if not flat:
                    return True
                column += len(part.flat)
            elif isinstance(part, tuple):
                pending.extend(
                    (indent, flat, item)
                    for item in reversed(cast(tuple[_Doc, ...], part))
                )
            elif isinstance(part, _Nest):
                pending.append((indent + 2, flat, part.doc))
            elif isinstance(part, _Group):
                pending.append((indent, flat, part.doc))
            else:
                raise TypeError(f"Unexpected layout node: {type(part).__name__}")
        return column <= width

    pending = [(0, False, doc)]
    out = []
    column = 0
    while pending:
        indent, flat, part = pending.pop()
        if isinstance(part, str):
            out.append(part)
            column += len(part)
        elif isinstance(part, _Break):
            if flat:
                out.append(part.flat)
                column += len(part.flat)
            else:
                out.append("\n" + " " * indent)
                column = indent
        elif isinstance(part, tuple):
            pending.extend(
                (indent, flat, item) for item in reversed(cast(tuple[_Doc, ...], part))
            )
        elif isinstance(part, _Nest):
            pending.append((indent + 2, flat, part.doc))
        elif isinstance(part, _Group):
            flat = flat or fits(column, [*pending, (indent, True, part.doc)])
            pending.append((indent, flat, part.doc))
        else:
            raise TypeError(f"Unexpected layout node: {type(part).__name__}")
    return "".join(out)


def _join(sep: _Doc, parts: list[_Doc]) -> _Doc:
    result = []
    for part in parts:
        if result:
            result.append(sep)
        result.append(part)
    return tuple(result)


def _delimited(left: str, parts: list[_Doc], right: str) -> _Doc:
    return _Group((left, _Nest(_join((",", _Break()), parts)), right))


def _sort(sort: smt.SortRef) -> str:
    if isinstance(sort, smt.ArraySortRef):
        domains = smt.domains(sort)
        if len(domains) == 1:
            domain = _sort(domains[0])
            if isinstance(domains[0], smt.ArraySortRef):
                domain = "(" + domain + ")"
            return domain + " → " + _sort(sort.range())
    return {"Int": "ℤ", "Real": "ℝ", "Bool": "Bool"}.get(sort.sexpr(), str(sort))


def _declarations(names: list[str], sorts: list[smt.SortRef]) -> list[str]:
    groups: list[tuple[list[str], smt.SortRef]] = []
    for name, sort in zip(names, sorts):
        if groups and groups[-1][1].eq(sort):
            groups[-1][0].append(name)
        else:
            groups.append(([name], sort))
    return [" ".join(names) + " : " + _sort(sort) for names, sort in groups]


_GREEK = dict(
    zip(
        "alpha beta gamma delta eps epsilon theta lambda mu pi rho sigma tau phi psi omega".split(),
        "α β γ δ ε ε θ λ μ π ρ σ τ φ ψ ω".split(),
    )
)
_SUBSCRIPT = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")


_FRESH_NAME = re.compile(r"(.+)!([0-9]+)")


class _Infix(NamedTuple):
    symbol: str
    precedence: int
    association: Literal["left", "right", "none"] = "none"
    breaks: bool = False


# The compact printer uses the default SMT backend's AST inspection.
_USE_COMPACT_PRINTER = smt.solver == smt.Z3SOLVER
if _USE_COMPACT_PRINTER:
    _INFIX = {
        smt.Z3_OP_IMPLIES: _Infix("→", 1, "right", True),
        smt.Z3_OP_OR: _Infix("∨", 2, "left", True),
        smt.Z3_OP_AND: _Infix("∧", 3, "left", True),
        smt.Z3_OP_EQ: _Infix("=", 4),
        smt.Z3_OP_LT: _Infix("<", 4),
        smt.Z3_OP_LE: _Infix("≤", 4),
        smt.Z3_OP_GT: _Infix(">", 4),
        smt.Z3_OP_GE: _Infix("≥", 4),
        smt.Z3_OP_ADD: _Infix("+", 5, "left"),
        smt.Z3_OP_SUB: _Infix("-", 5, "left"),
        smt.Z3_OP_MUL: _Infix("*", 6, "left"),
        smt.Z3_OP_DIV: _Infix("/", 6, "left"),
        smt.Z3_OP_IDIV: _Infix("div", 6, "left"),
        smt.Z3_OP_MOD: _Infix("mod", 6, "left"),
        smt.Z3_OP_POWER: _Infix("^", 8, "right"),
        smt.Z3_OP_SET_UNION: _Infix("∪", 5, "right", True),
        smt.Z3_OP_SET_INTERSECT: _Infix("∩", 6, "right", True),
        smt.Z3_OP_SET_DIFFERENCE: _Infix("∖", 5),
        smt.Z3_OP_SET_SUBSET: _Infix("⊆", 4),
        smt.Z3_OP_BADD: _Infix("+", 5, "left"),
        smt.Z3_OP_BSUB: _Infix("-", 5, "left"),
        smt.Z3_OP_BMUL: _Infix("*", 6, "left"),
        smt.Z3_OP_BAND: _Infix("&", 3),
        smt.Z3_OP_BXOR: _Infix("⊕", 3),
        smt.Z3_OP_BOR: _Infix("|", 3),
        smt.Z3_OP_BSHL: _Infix("<<", 4),
        smt.Z3_OP_BLSHR: _Infix(">>ᵤ", 4),
        smt.Z3_OP_BASHR: _Infix(">>ₛ", 4),
        smt.Z3_OP_BSDIV: _Infix("/ₛ", 6, "left"),
        smt.Z3_OP_BUDIV: _Infix("/ᵤ", 6, "left"),
        smt.Z3_OP_SLT: _Infix("<ₛ", 4),
        smt.Z3_OP_SLEQ: _Infix("≤ₛ", 4),
        smt.Z3_OP_SGT: _Infix(">ₛ", 4),
        smt.Z3_OP_SGEQ: _Infix("≥ₛ", 4),
        smt.Z3_OP_ULT: _Infix("<ᵤ", 4),
        smt.Z3_OP_ULEQ: _Infix("≤ᵤ", 4),
        smt.Z3_OP_UGT: _Infix(">ᵤ", 4),
        smt.Z3_OP_UGEQ: _Infix("≥ᵤ", 4),
    }
    _PREFIX = {
        smt.Z3_OP_NOT: ("¬", 4),
        smt.Z3_OP_UMINUS: ("-", 7),
        smt.Z3_OP_BNEG: ("-", 7),
        smt.Z3_OP_BNOT: ("~", 7),
    }
    _SORT_DISPATCH_INFIX = (
        (notation.add, _INFIX[smt.Z3_OP_ADD]),
        (notation.radd, _INFIX[smt.Z3_OP_ADD]),
        (notation.sub, _INFIX[smt.Z3_OP_SUB]),
        (notation.mul, _INFIX[smt.Z3_OP_MUL]),
        (notation.rmul, _INFIX[smt.Z3_OP_MUL]),
        (notation.matmul, _Infix("@", 6, "left")),
        (notation.div, _INFIX[smt.Z3_OP_DIV]),
        (notation.and_, _INFIX[smt.Z3_OP_AND]),
        (notation.or_, _INFIX[smt.Z3_OP_OR]),
        (notation.lt, _INFIX[smt.Z3_OP_LT]),
        (notation.le, _INFIX[smt.Z3_OP_LE]),
        (notation.gt, _INFIX[smt.Z3_OP_GT]),
        (notation.ge, _INFIX[smt.Z3_OP_GE]),
        (notation.eq, _INFIX[smt.Z3_OP_EQ]),
        (notation.ne, _Infix("≠", 4)),
    )
    _SORT_DISPATCH_PREFIX = (
        (notation.neg, _PREFIX[smt.Z3_OP_UMINUS]),
        (notation.invert, _PREFIX[smt.Z3_OP_NOT]),
    )
    _POSTFIX = {smt.Z3_OP_SET_COMPLEMENT: "ᶜ"}
else:
    _INFIX = _PREFIX = _POSTFIX = {}
    _SORT_DISPATCH_INFIX = _SORT_DISPATCH_PREFIX = ()

_custom_infix: dict[smt.FuncDeclRef, _Infix] = {}
# Theory modules can opt a specific declaration into paired delimiters.
_delimiters: dict[smt.FuncDeclRef, tuple[str, str]] = {}


def register_infix(
    decl: smt.FuncDeclRef,
    symbol: str,
    precedence: int,
    *,
    association: Literal["left", "right", "none"] = "none",
    breaks: bool = False,
) -> None:
    """Set a binary display rule with precedence from 1 to 8 (tightest)."""
    if decl.arity() != 2:
        raise ValueError("Infix notation requires a binary declaration")
    if not 1 <= precedence <= 8:
        raise ValueError("Infix precedence must be between 1 and 8")
    _custom_infix[decl] = _Infix(symbol, precedence, association, breaks)


class _Printer:
    def __init__(self, expressions: list[smt.ExprRef]):
        self.infix = {
            decl: rule
            for dispatch, rule in _SORT_DISPATCH_INFIX
            for decl in dispatch.methods.values()
            if isinstance(decl, smt.FuncDeclRef) and decl.arity() == 2
        }
        self.prefix = {
            decl: rule
            for dispatch, rule in _SORT_DISPATCH_PREFIX
            for decl in dispatch.methods.values()
            if isinstance(decl, smt.FuncDeclRef) and decl.arity() == 1
        }
        # Collect binder and declaration names across the whole display. This lets
        # us rank fresh suffixes per base and avoid collisions with existing names.
        decls = {}
        binder_names = set()
        seen: dict[int, int] = {}
        pending = [(expr, 0) for expr in reversed(expressions)]
        self.too_deep = False
        while pending:
            expr, depth = pending.pop()
            # Rendering uses several Python frames per expression level.
            if depth > 150:
                self.too_deep = True
                return
            expr_id = expr.get_id()
            if seen.get(expr_id, -1) >= depth:
                continue
            seen[expr_id] = depth
            if isinstance(expr, smt.QuantifierRef):
                binder_names.update(
                    str(expr.var_name(i)) for i in range(expr.num_vars())
                )
                pending.append((expr.body(), depth + 1))
            elif smt.is_app(expr):
                if (
                    smt.is_uninterp(expr)
                    or smt.is_constructor(expr)
                    or smt.is_accessor(expr)
                ):
                    decls.setdefault(expr.decl(), str(expr.decl().name()))
                pending.extend((arg, depth + 1) for arg in reversed(expr.children()))
        raw = set(decls.values())
        suffixes: dict[str, set[int]] = {}
        for name in raw | binder_names:
            if match := _FRESH_NAME.fullmatch(name):
                base, suffix = match.groups()
                suffixes.setdefault(base, set()).add(int(suffix))
        self.fresh_indices = {
            (base, suffix): str(i).translate(_SUBSCRIPT)
            for base, numbers in suffixes.items()
            for i, suffix in enumerate(sorted(numbers))
        }
        self.names: dict[smt.FuncDeclRef, str] = {}
        self.used: set[str] = set()
        for decl, name in decls.items():
            alias = self.alias(name)
            if alias != name and (alias in raw or alias in self.used):
                alias = name
            self.names[decl] = self.fresh(alias, raw if alias in self.used else set())
            self.used.add(self.names[decl])

    def alias(self, name: str) -> str:
        if match := _FRESH_NAME.fullmatch(name):
            base, suffix = match.groups()
            return _GREEK.get(base, base) + self.fresh_indices[base, int(suffix)]
        return _GREEK.get(name, name)

    def fresh(self, name: str, reserved: set[str]) -> str:
        if name not in self.used and name not in reserved:
            return name
        index = 1
        while f"{name}′{index}" in self.used or f"{name}′{index}" in reserved:
            index += 1
        return f"{name}′{index}"

    def expr(
        self, expr: smt.ExprRef, outer: int = 0, bound: tuple[str, ...] = ()
    ) -> _Doc:
        def child(term: smt.ExprRef, prec: int = 0) -> _Doc:
            return self.expr(term, prec, bound)

        def wrap(doc: _Doc, prec: int) -> _Doc:
            return ("(", doc, ")") if prec < outer else doc

        if smt.is_var(expr):
            index = smt.get_var_index(expr)
            return bound[index] if index < len(bound) else expr.sexpr()
        if isinstance(expr, smt.QuantifierRef):
            raw = [str(expr.var_name(i)) for i in range(expr.num_vars())]
            sorts = [expr.var_sort(i) for i in range(expr.num_vars())]
            reserved = set(raw)
            names = []
            for name in raw:
                alias = self.alias(name)
                if alias in self.used or (alias != name and alias in raw):
                    alias = name
                name = self.fresh(alias, reserved - {name})
                names.append(name)
                self.used.add(name)
            body = self.expr(expr.body(), bound=tuple(reversed(names)) + bound)
            self.used.difference_update(names)
            symbol = "∀" if expr.is_forall() else "∃" if expr.is_exists() else "λ"
            header = symbol + ", ".join(_declarations(names, sorts)) + ","
            return wrap(_Group((header, _Nest((_Break(), body)))), 0)

        decl = expr.decl()
        kind = decl.kind()
        args = expr.children()
        if smt.is_if(expr):
            cases, default = ite_to_cases(expr)
            clauses: list[_Doc] = [
                ("else if " if i else "if ", child(guard, 1), " then ", child(value, 1))
                for i, (guard, value) in enumerate(cases)
            ]
            clauses.append(("else ", child(default, 1)))
            return wrap(_Group(_join(_Break(), clauses)), 0)
        infix = _custom_infix.get(decl) or _INFIX.get(kind) or self.infix.get(decl)
        if infix is not None and len(args) >= 2:
            symbol, prec, association, breaks = infix
            left_prec = prec if association == "left" else prec + 1
            right_prec = prec if association == "right" else prec + 1
            if smt.is_implies(expr) and isinstance(args[-1], smt.QuantifierRef):
                right_prec = 0
            parts = [child(args[0], left_prec)]
            parts.extend(child(arg, prec + 1) for arg in args[1:-1])
            parts.append(child(args[-1], right_prec))
            separator = (" " + symbol, _Break()) if breaks else " " + symbol + " "
            return wrap(_Group(_join(separator, parts)), prec)
        prefix = _PREFIX.get(kind) or self.prefix.get(decl)
        if prefix is not None:
            symbol, prec = prefix
            return wrap((symbol, child(args[0], prec + 1)), prec)
        if decl in _delimiters:
            left, right = _delimiters[decl]
            return (left, child(args[0], 1), right)
        if kind in _POSTFIX:
            return wrap((child(args[0], 9), _POSTFIX[kind]), 9)
        if smt.is_accessor(decl):
            return (child(args[0], 9), ".", self.names[decl])
        if smt.is_select(expr):
            return (
                child(args[0], 9),
                _delimited("[", [child(a) for a in args[1:]], "]"),
            )
        if smt.is_int_value(expr) or smt.is_rational_value(expr):
            value = str(expr)
            prec = 6 if "/" in value else 7 if value.startswith("-") else 9
            return wrap(value, prec)
        if not args:
            return self.names.get(decl, expr.sexpr())
        name = self.names.get(decl, str(decl.name()))
        if decl not in self.names and decl.params():
            name += "[" + ", ".join(str(param) for param in decl.params()) + "]"
        return _delimited(name + "(", [child(arg) for arg in args], ")")


def pretty_expr(expr: smt.ExprRef, *, width: int = 80) -> str:
    """Display an SMT expression using compact mathematical notation."""
    if not _USE_COMPACT_PRINTER:
        return str(expr)
    printer = _Printer([expr])
    if printer.too_deep:
        return expr.sexpr()
    return _layout(printer.expr(expr), width)


def pretty_goal(goal: "Goal", *, width: int = 80) -> str:
    """Display locals, numbered hypotheses, and the conclusion."""
    if not _USE_COMPACT_PRINTER or goal.is_empty():
        return repr(goal)
    printer = _Printer([*goal.sig, *goal.ctx, goal.goal])
    if printer.too_deep:
        rows = [f"{local.sexpr()} : {local.sort().sexpr()}" for local in goal.sig]
        rows.extend(f"{i}: {hyp.sexpr()}" for i, hyp in enumerate(goal.ctx))
        rows.append(f"⊢ {goal.goal.sexpr()}")
        return "\n".join(rows)
    rows = _declarations(
        [printer.names.get(local.decl(), str(local)) for local in goal.sig],
        [local.sort() for local in goal.sig],
    )
    hypotheses = [
        _layout((f"{index}: ", _Nest(printer.expr(hyp))), width)
        for index, hyp in enumerate(goal.ctx)
    ]
    conclusion = _layout(("⊢ ", _Nest(printer.expr(goal.goal))), width)
    if hypotheses:
        rows.extend(hypotheses)
        longest = max(
            len(line) for row in [*hypotheses, conclusion] for line in row.splitlines()
        )
        rows.append("─" * max(1, min(width, longest)))
    rows.append(conclusion)
    return "\n".join(rows)
