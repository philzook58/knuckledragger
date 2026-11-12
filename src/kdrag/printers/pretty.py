"""Compact, width-aware display of SMT expressions and tactic goals."""

from dataclasses import dataclass
import re
from typing import TYPE_CHECKING, NamedTuple, cast

from kdrag import smt
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
            else:
                pending.append((indent, flat, part.doc))
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
        else:
            flat = flat or fits(column, [*pending, (indent, True, part.doc)])
            pending.append((indent, flat, part.doc))
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
    if (
        isinstance(sort, smt.ArraySortRef)
        and smt.Z3_get_array_arity(sort.ctx_ref(), sort.ast) == 1  # type: ignore[ty:unresolved-attribute]
    ):
        domain = _sort(sort.domain())
        if isinstance(sort.domain(), smt.ArraySortRef):
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


def _alias(name: str) -> str:
    base, bang, digits = name.rpartition("!")
    if bang and re.fullmatch("[0-9]+", digits):
        return _GREEK.get(base, base) + digits.translate(_SUBSCRIPT)
    return _GREEK.get(name, name)


class _Infix(NamedTuple):
    symbol: str
    precedence: int
    association: str = ""
    breaks: bool = False


_Z3_AST = hasattr(smt, "Z3_OP_IMPLIES") and hasattr(smt, "is_if")
_INFIX = (
    {
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
    }
    if _Z3_AST
    else {}
)
_PREFIX = {smt.Z3_OP_NOT: ("¬", 4), smt.Z3_OP_UMINUS: ("-", 7)} if _Z3_AST else {}
# Theory modules can opt a specific declaration into paired delimiters.
_delimiters: dict[smt.FuncDeclRef, tuple[str, str]] = {}


class _Printer:
    def __init__(self, expressions: list[smt.ExprRef]):
        decls = {}
        seen = set()
        pending = list(reversed(expressions))
        while pending:
            expr = pending.pop()
            if expr.get_id() in seen:
                continue
            seen.add(expr.get_id())
            if isinstance(expr, smt.QuantifierRef):
                pending.append(expr.body())
            elif smt.is_app(expr):
                if expr.decl().kind() in (
                    smt.Z3_OP_UNINTERPRETED,  # type: ignore[ty:unresolved-attribute]
                    smt.Z3_OP_DT_CONSTRUCTOR,  # type: ignore[ty:unresolved-attribute]
                    smt.Z3_OP_DT_ACCESSOR,  # type: ignore[ty:unresolved-attribute]
                ):
                    decls.setdefault(expr.decl(), str(expr.decl().name()))
                pending.extend(reversed(expr.children()))
        raw = set(decls.values())
        self.names: dict[smt.FuncDeclRef, str] = {}
        self.used: set[str] = set()
        for decl, name in decls.items():
            alias = _alias(name)
            if alias != name and (alias in raw or alias in self.used):
                alias = name
            self.names[decl] = self.fresh(alias, raw if alias in self.used else set())
            self.used.add(self.names[decl])

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
                alias = _alias(name)
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
        if kind == smt.Z3_OP_ITE:  # type: ignore[ty:unresolved-attribute]
            cases, default = ite_to_cases(expr)
            clauses: list[_Doc] = [
                ("else if " if i else "if ", child(guard, 1), " then ", child(value, 1))
                for i, (guard, value) in enumerate(cases)
            ]
            clauses.append(("else ", child(default, 1)))
            return wrap(_Group(_join(_Break(), clauses)), 0)
        if kind in _INFIX and len(args) >= 2:
            symbol, prec, association, breaks = _INFIX[kind]
            left_prec = prec if association == "left" else prec + 1
            right_prec = prec if association == "right" else prec + 1
            if kind == smt.Z3_OP_IMPLIES and isinstance(args[-1], smt.QuantifierRef):  # type: ignore[ty:unresolved-attribute]
                right_prec = 0
            parts = [child(args[0], left_prec)]
            parts.extend(child(arg, prec + 1) for arg in args[1:-1])
            parts.append(child(args[-1], right_prec))
            separator = (" " + symbol, _Break()) if breaks else " " + symbol + " "
            return wrap(_Group(_join(separator, parts)), prec)
        if kind in _PREFIX:
            symbol, prec = _PREFIX[kind]
            return wrap((symbol, child(args[0], prec + 1)), prec)
        if decl in _delimiters:
            left, right = _delimiters[decl]
            return (left, child(args[0], 1), right)
        if kind == smt.Z3_OP_SELECT:  # type: ignore[ty:unresolved-attribute]
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
    if not _Z3_AST:
        return str(expr)
    return _layout(_Printer([expr]).expr(expr), width)


def pretty_goal(goal: "Goal", *, width: int = 80) -> str:
    """Display locals, numbered hypotheses, and the conclusion."""
    if not _Z3_AST or goal.is_empty():
        return repr(goal)
    printer = _Printer([*goal.sig, *goal.ctx, goal.goal])
    rows = _declarations(
        [printer.names.get(local.decl(), str(local)) for local in goal.sig],
        [local.sort() for local in goal.sig],
    )
    rows.extend(
        _layout((f"{index}: ", _Nest(printer.expr(hyp))), width)
        for index, hyp in enumerate(goal.ctx)
    )
    rows.append(_layout(("⊢ ", _Nest(printer.expr(goal.goal))), width))
    return "\n".join(rows)
