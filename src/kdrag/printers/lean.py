import re
import subprocess

import kdrag as kd
import kdrag.smt as smt
from kdrag.printers._layout import _Break, _Doc, _Group, _Nest, _join, _layout


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


# Lean precedence and associativity from Init.Notation. Arrow binds below Or.
_PROP_INFIX = (
    {
        smt.Z3_OP_IMPLIES: ("→", 25, "right"),
        smt.Z3_OP_OR: ("∨", 30, "right"),
        smt.Z3_OP_AND: ("∧", 35, "right"),
        smt.Z3_OP_LT: ("<", 50, "none"),
        smt.Z3_OP_LE: ("≤", 50, "none"),
        smt.Z3_OP_GT: (">", 50, "none"),
        smt.Z3_OP_GE: ("≥", 50, "none"),
        smt.Z3_OP_ADD: ("+", 65, "left"),
        smt.Z3_OP_SUB: ("-", 65, "left"),
        smt.Z3_OP_MUL: ("*", 70, "left"),
    }
    if smt.solver == smt.Z3SOLVER
    else {}
)

_IDENT = re.compile(r"[a-zA-Z_][a-zA-Z0-9_']*")
_KEYWORDS = frozenset(
    "if then else fun forall let in match nomatch with by do have show from "
    "calc suffices sorry rfl Type Sort at where as return try catch for unless "
    "def abbrev theorem lemma example axiom opaque variable namespace section end "
    "import open export structure inductive class instance deriving set_option "
    "true false _ _root_".split()
)
_BUILTIN_NAMES = {"Int", "ℝ", "Prop", "True", "False"}


def _identifier(name: str) -> str:
    if not name or any(c in "«»" or ord(c) < 32 for c in name):
        raise ValueError(f"Cannot write Lean identifier {name!r}")
    if _IDENT.fullmatch(name) and name not in _KEYWORDS:
        return name
    return f"«{name}»"


def _qualified(name: str) -> str:
    return ".".join(_identifier(part) for part in name.split("."))


class _PropPrinter:
    def __init__(self, expr: smt.ExprRef, fully_parenthesized: bool):
        self.full = fully_parenthesized
        if smt.solver != smt.Z3SOLVER:
            raise NotImplementedError(
                "Lean proposition export requires the Z3 AST backend"
            )
        if not smt.is_bool(expr):
            raise TypeError("Expected a Boolean SMT expression")
        self.used = {_identifier(name) for name in _BUILTIN_NAMES}
        self.free_names: dict[str, smt.SortRef | smt.FuncDeclRef] = {}
        # Reserve free names before choosing names for the de Bruijn binders.
        for term in kd.utils.subterms(expr, into_binder=True):
            self.sort(term.sort())
            if isinstance(term, smt.QuantifierRef):
                for i in range(term.num_vars()):
                    self.sort(term.var_sort(i))
            elif smt.is_uninterp(term):
                self.name(term.decl())

    def name(self, decl: smt.SortRef | smt.FuncDeclRef) -> str:
        raw = str(decl.name())
        name = _qualified(raw)
        previous = self.free_names.get(name)
        if raw in _BUILTIN_NAMES or (previous is not None and not previous.eq(decl)):
            raise ValueError(f"Ambiguous Lean name {name}")
        self.free_names[name] = decl
        self.used.add(name.split(".", 1)[0])
        return name

    def sort(self, sort: smt.SortRef) -> str:
        if smt.is_bool_sort(sort):
            return "Prop"
        if smt.is_int_sort(sort):
            return "Int"
        if smt.is_real_sort(sort):
            return "ℝ"
        if isinstance(sort, smt.ArraySortRef):
            domains = smt.domains(sort)
            if len(domains) == 1:
                domain = self.sort(domains[0])
                if isinstance(domains[0], smt.ArraySortRef):
                    domain = f"({domain})"
                return f"{domain} → {self.sort(sort.range())}"
        if sort.kind() == smt.Z3_UNINTERPRETED_SORT:  # type: ignore[ty:missing-attribute]
            return self.name(sort)
        raise NotImplementedError(f"Unsupported Lean export sort: {sort}")

    def expr(
        self, expr: smt.ExprRef, outer: int = 0, bound: tuple[str, ...] = ()
    ) -> _Doc:
        def child(term: smt.ExprRef, prec: int = 0) -> _Doc:
            return self.expr(term, prec, bound)

        def wrap(doc: _Doc, prec: int) -> _Doc:
            return ("(", doc, ")") if self.full or prec < outer else doc

        def apply(head: _Doc, args: list[smt.ExprRef]) -> _Doc:
            if self.full:
                for arg in args:
                    head = ("(", head, " ", child(arg), ")")
                return head
            parts: list[_Doc] = []
            for arg in args:
                parts.extend((_Break(), child(arg, 1024)))
            return wrap(_Group((head, _Nest(tuple(parts)))), 1023)

        def infix(symbol: str, prec: int, assoc: str, args: list[smt.ExprRef]) -> _Doc:
            sep = (" " + symbol, _Break())
            parts = [
                child(
                    arg,
                    prec
                    if (i == 0 and assoc == "left")
                    or (i == len(args) - 1 and assoc == "right")
                    else prec + 1,
                )
                for i, arg in enumerate(args)
            ]
            if not self.full:
                return wrap(_Group(_join(sep, parts)), prec)
            if assoc == "right":
                doc = parts[-1]
                for part in reversed(parts[:-1]):
                    doc = ("(", part, sep, doc, ")")
            else:
                doc = parts[0]
                for part in parts[1:]:
                    doc = ("(", doc, sep, part, ")")
            return _Group(doc)

        if smt.is_var(expr):
            i = smt.get_var_index(expr)
            if i >= len(bound):
                raise ValueError(f"Unbound SMT variable: {expr}")
            return bound[i]
        if isinstance(expr, smt.QuantifierRef):
            names = []
            groups: list[tuple[list[str], str]] = []
            for i in range(expr.num_vars()):
                raw = str(expr.var_name(i))
                name = _identifier(raw)
                index = 1
                while name in self.used:
                    name = _identifier(f"{raw}_{index}")
                    index += 1
                self.used.add(name)
                names.append(name)
                sort = self.sort(expr.var_sort(i))
                if groups and groups[-1][1] == sort:
                    groups[-1][0].append(name)
                else:
                    groups.append(([name], sort))
            body = self.expr(expr.body(), bound=tuple(reversed(names)) + bound)
            self.used.difference_update(names)
            binders = " ".join(f"({' '.join(vs)} : {sort})" for vs, sort in groups)
            prefix = "∀ " if expr.is_forall() else "∃ " if expr.is_exists() else "fun "
            suffix = " =>" if expr.is_lambda() else ","
            return wrap(
                _Group((prefix + binders + suffix, _Nest((_Break(), body)))),
                0,
            )

        if isinstance(expr, smt.IntNumRef):
            return f"({expr.as_long()} : Int)"
        if isinstance(expr, smt.RatNumRef):
            numerator, denominator = (
                expr.numerator_as_long(),
                expr.denominator_as_long(),
            )
            if denominator == 1:
                return f"({numerator} : ℝ)"
            return f"(({numerator} : ℝ) / {denominator})"
        if smt.is_true(expr):
            return "True"
        if smt.is_false(expr):
            return "False"
        if not smt.is_app(expr):
            raise NotImplementedError(f"Unsupported Lean export term: {expr}")

        decl = expr.decl()
        args = expr.children()
        kind = decl.kind()
        if smt.is_uninterp(decl):
            name = self.name(decl)
            return apply(name, args) if args else name
        if smt.is_select(expr) and len(args) == 2:
            return apply(child(args[0], 1023), args[1:])
        if smt.is_if(expr):
            condition, yes, no = args
            return wrap(
                _Group(
                    (
                        "if ",
                        child(condition),
                        _Nest(
                            (
                                _Break(),
                                "then ",
                                child(yes),
                                _Break(),
                                "else ",
                                child(no),
                            )
                        ),
                    )
                ),
                0,
            )
        if smt.is_eq(expr):
            if smt.is_bool(args[0]):
                return infix("↔", 20, "none", args)
            return infix("=", 50, "none", args)
        if smt.is_distinct(expr) and len(args) == 2:
            return infix("≠", 50, "none", args)
        if smt.is_not(expr):
            # A bare negation in an argument can absorb the next argument.
            return wrap(("¬ ", child(args[0], 40)), 40)
        if smt.is_neg(expr):
            return wrap(("-", child(args[0], 76)), 75)
        if smt.is_to_real(expr):
            return ("((", child(args[0]), " : Int) : ℝ)")
        if rule := _PROP_INFIX.get(kind):
            if not args:
                return "True" if smt.is_and(expr) else "False"
            if len(args) == 1:
                return child(args[0], outer)
            return infix(*rule, args)
        raise NotImplementedError(f"Unsupported Lean export operator: {decl.name()}")


def of_prop(
    expr: smt.ExprRef, *, fully_parenthesized: bool = False, width: int = 100
) -> str:
    """Emit a Lean proposition in a context that declares its free symbols.

    SMT Booleans become propositions and unary arrays become functions.
    Dots in free symbol names are treated as Lean namespace separators.
    Use Mathlib for reals and `open Classical` for undecidable conditions.

    >>> x = smt.Int("x")
    >>> of_prop(smt.ForAll(x, smt.Implies(x > 0, x + 1 > 0)))
    '∀ (x : Int), x > (0 : Int) → x + (1 : Int) > (0 : Int)'
    """
    return _layout(_PropPrinter(expr, fully_parenthesized).expr(expr), width)


def guard_prop(expr: smt.ExprRef, *, width: int = 100) -> str:
    """Emit a Lean check that both renderings elaborate to the same proposition."""
    readable = _PropPrinter(expr, False).expr(expr)
    explicit = _PropPrinter(expr, True).expr(expr)
    return _layout(
        (
            "#guard_expr",
            _Nest((_Break(), "(", readable, ") =ₐ", _Break(), "(", explicit, ")")),
        ),
        width,
    )
