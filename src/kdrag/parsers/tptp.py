"""
TPTP is a format for automated theorem provers.
Read more about it at https://www.tptp.org/
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Optional, cast

import lark  # type: ignore[reportMissingImports]
import kdrag.smt as smt

# https://github.com/inpefess/tptp-lark-parser/blob/master/tptp_lark_parser/resources/TPTP.lark
# https://github.com/TPTPWorld/SyntaxBNF/blob/master/SyntaxBNF-v9.0.0.8
fof_grammar = r"""
start                : (cnf | fof | tff | thf)*
cnf       : "cnf" "(" NAME "," FORMULA_ROLE "," cnf_formula ")"  "."
fof       : "fof" "(" NAME "," FORMULA_ROLE "," fof_formula ")"  "." 
tff       : "tff" "(" NAME "," FORMULA_ROLE "," tff_formula ")"  "."
thf       : "thf" "(" NAME "," FORMULA_ROLE "," thf_formula ")"  "."

FORMULA_ROLE         :  "axiom" | "conjecture" | "type"

?fof_formula         :  fof_unit_formula "<=>" fof_unit_formula -> iff
                     | fof_unit_formula "=>" fof_unit_formula -> implies
                     | fof_unit_formula "<=" fof_unit_formula -> reverse_implies
                     | fof_or_formula
?fof_or_formula       : fof_and_formula  ("|" fof_and_formula)*
?fof_and_formula      : fof_unit_formula ("&" fof_unit_formula)*
?fof_unit_formula     : "~" fof_unit_formula -> not_formula 
                      | term "!=" term      -> diseq
                      | term "=" term  ->      eq
                      | "(" fof_formula ")" 
                      | term  -> predicate
                      | "!" "[" fof_variable_list "]" ":" fof_unit_formula -> forall
                      | "?" "[" fof_variable_list "]" ":" fof_unit_formula -> exists

?thf_formula          : tff_type_formula
                     | thf_unit_formula "<=>" thf_unit_formula -> iff
                     | thf_unit_formula "=>" thf_unit_formula -> implies
                     | thf_unit_formula "<=" thf_unit_formula -> reverse_implies
                     | thf_or_formula
?thf_or_formula       : thf_and_formula  ("|" thf_and_formula)*
?thf_and_formula      : thf_unit_formula ("&" thf_unit_formula)*
?thf_unit_formula     : "~" thf_unit_formula -> not_formula
                      | thf_term "!=" thf_term -> diseq
                      | thf_term "=" thf_term -> eq
                      | "(" thf_formula ")"
                      | thf_term -> predicate
                      | "!" "[" fof_variable_list "]" ":" thf_unit_formula -> forall
                      | "?" "[" fof_variable_list "]" ":" thf_unit_formula -> exists

?thf_term             : thf_app
?thf_app              : thf_app "@" thf_atom -> thf_app
                      | thf_atom
?thf_atom             : term
                      | "(" thf_term ")"
                      | thf_lambda
thf_lambda            : "^" "[" fof_variable_list "]" ":" thf_term

?tff_formula          : tff_type_formula
                     | fof_formula

tff_type_formula     : term ":" tff_type

tff_type             : tff_type_product (">" tff_type)*
tff_type_product     : tff_type_atom ("*" tff_type_atom)*
tff_type_atom        : NAME
                     | TTYPE
                     | BOOLTYPE
                     | "(" tff_type ")"

                      
?cnf_formula          : disjunction | "(" disjunction ")"
disjunction         : literal ("|" cnf_formula)*
literal              : atomic_formula -> poslit 
                    | "~" atomic_formula -> neglit
                    | term "!=" term  -> diseq
                    | term "=" term -> eq
atomic_formula       : term


arguments            : term ("," term)*

term                :  NAME -> const
            |        | variable -> var
                     |  NAME "(" arguments ")" -> fun_app


FOF_QUANTIFIER       : "!" | "?"
fof_variable_list    : tff_typed_variable ("," tff_typed_variable)*

tff_typed_variable   : variable (":" tff_type)?

?variable : UPPER_WORD

NONASSOC_CONNECTIVE  : "<=>" | "=>" | "<="  // | "<~>" | "~|" | "~&"

NAME                 : LOWER_WORD
UPPER_WORD           : UPPER_ALPHA ALPHA_NUMERIC*
LOWER_WORD           : LOWER_ALPHA ALPHA_NUMERIC*
NUMERIC              : "0".."9"
LOWER_ALPHA          : "a".."z"
UPPER_ALPHA          : "A".."Z"
ALPHA_NUMERIC        : (LOWER_ALPHA | UPPER_ALPHA | NUMERIC | "_") 
TTYPE                : "$tType"
BOOLTYPE             : "$o"

%import common.WS
%ignore WS
%ignore /%[^\n]*/

"""


term_parser = lark.Lark(fof_grammar, start="term", parser="lalr", cache=False)
fof_parser = lark.Lark(fof_grammar, start="start", parser="lalr", cache=True)


def test():
    """
    >>> term_parser.parse("f(Xy1,g(y23))")
    Tree('fun_app', [Token('NAME', 'f'), Tree(Token('RULE', 'arguments'), [Tree('var', [Token('UPPER_WORD', 'Xy1')]), Tree('fun_app', [Token('NAME', 'g'), Tree(Token('RULE', 'arguments'), [Tree('const', [Token('NAME', 'y23')])])])])])
    """


# untyped formula get interpreted into T
T = smt.DeclareSort("T")


class FormulaRole(Enum):
    AXIOM = "axiom"
    CONJECTURE = "conjecture"


@dataclass
class TPTPFormulaEntry:
    name: str
    role: FormulaRole
    formula: smt.BoolRef


class TPTPTransformer(lark.Transformer):
    def __init__(self, sort: smt.SortRef | None = None, thf_mode: bool = False):
        super().__init__()
        self.sort = sort if sort is not None else T
        self.sorts: dict[str, smt.SortRef] = {"T": self.sort}
        self.funcs: dict[tuple[str, int], smt.FuncDeclRef] = {}
        self.preds: dict[tuple[str, int], smt.FuncDeclRef | smt.BoolRef] = {}
        self.vars: dict[str, smt.ExprRef] = {}
        self.consts: dict[str, smt.ExprRef] = {}
        self.const_sorts: dict[str, smt.SortRef] = {}
        self.func_sigs: dict[str, tuple[list[smt.SortRef], Optional[smt.SortRef]]] = {}
        self.thf_mode = thf_mode

    def start(self, items):
        return [item for item in items if item is not None]

    def cnf(self, items):
        name, role, formula = items
        role_value = str(role)
        if role_value == FormulaRole.AXIOM.value:
            return TPTPFormulaEntry(str(name), FormulaRole.AXIOM, formula)
        if role_value == FormulaRole.CONJECTURE.value:
            return TPTPFormulaEntry(str(name), FormulaRole.CONJECTURE, formula)
        return None

    def fof(self, items):
        name, role, formula = items
        role_value = str(role)
        if role_value == FormulaRole.AXIOM.value:
            return TPTPFormulaEntry(str(name), FormulaRole.AXIOM, formula)
        if role_value == FormulaRole.CONJECTURE.value:
            return TPTPFormulaEntry(str(name), FormulaRole.CONJECTURE, formula)
        return None

    def tff(self, items):
        name, role, formula = items
        role_value = str(role)
        if role_value == FormulaRole.AXIOM.value:
            return TPTPFormulaEntry(str(name), FormulaRole.AXIOM, formula)
        if role_value == FormulaRole.CONJECTURE.value:
            return TPTPFormulaEntry(str(name), FormulaRole.CONJECTURE, formula)
        return None

    def thf(self, items):
        name, role, formula = items
        role_value = str(role)
        if role_value == FormulaRole.AXIOM.value:
            return TPTPFormulaEntry(str(name), FormulaRole.AXIOM, formula)
        if role_value == FormulaRole.CONJECTURE.value:
            return TPTPFormulaEntry(str(name), FormulaRole.CONJECTURE, formula)
        return None

    def const(self, items):
        name = str(items[0])
        const = self.consts.get(name)
        if const is not None:
            return const
        if self.thf_mode and name in self.func_sigs:
            sort = self._function_sort_from_sig(self.func_sigs[name])
        else:
            sort = self.const_sorts.get(name, self.sort)
        const = smt.Const(name, sort)
        self.consts[name] = const
        return const

    def var(self, items):
        name = str(items[0])
        if name not in self.vars:
            self.vars[name] = smt.Const(name, self.sort)
        return self.vars[name]

    def arguments(self, items):
        return list(items)

    def fun_app(self, items):
        name = str(items[0])
        args = items[1:]
        if len(args) == 1 and isinstance(args[0], list):
            args = args[0]
        fn = self._func(name, len(args))
        return fn(*args)

    def predicate(self, items):
        term = items[0]
        try:
            if term.sort() == smt.BoolSort():
                return term
        except Exception:
            pass
        name = term.decl().name()
        args = list(term.children())
        pred = self._pred(name, len(args))
        return pred if len(args) == 0 else pred(*args)

    def atomic_formula(self, items):
        return self.predicate(items)

    def poslit(self, items):
        return items[0]

    def neglit(self, items):
        return smt.Not(items[0])

    def eq(self, items):
        return smt.Eq(items[0], items[1])

    def diseq(self, items):
        return items[0] != items[1]

    def not_formula(self, items):
        return smt.Not(items[0])

    def fof_or_formula(self, items):
        if len(items) == 1:
            return items[0]
        return smt.Or(*items)

    def fof_and_formula(self, items):
        if len(items) == 1:
            return items[0]
        return smt.And(*items)

    def iff(self, items):
        left, right = items
        return smt.And(smt.Implies(left, right), smt.Implies(right, left))

    def implies(self, items):
        return smt.Implies(items[0], items[1])

    def reverse_implies(self, items):
        return smt.Implies(items[1], items[0])

    def cnf_formula(self, items):
        return items[0]

    def disjunction(self, items):
        flat = []
        for item in items:
            if isinstance(item, smt.ExprRef) and smt.is_or(item):
                flat.extend(item.children())
            else:
                flat.append(item)
        if len(flat) == 1:
            return flat[0]
        return smt.Or(*flat)

    def forall(self, items):
        vs, body = items
        return smt.ForAll(vs, body)

    def exists(self, items):
        vs, body = items
        return smt.Exists(vs, body)

    def fof_variable_list(self, items):
        return [self._as_var(item) for item in items]

    def tff_typed_variable(self, items):
        if len(items) == 1:
            return self._as_var(items[0])
        var = items[0]
        name = self._term_name(var)
        sort = self._type_repr_to_sort(
            cast(str | list[Any] | tuple[str, Any, Any], items[1])
        )
        if isinstance(sort, tuple):
            sort = self._function_sort_from_sig(sort) if self.thf_mode else self.sort
        if sort is None:
            sort = self.sort
        v = smt.Const(name, sort)
        self.vars[name] = v
        return v

    def tff_type_formula(self, items):
        term, type_repr = items
        name = self._term_name(term)
        type_repr = cast(
            str | list[Any] | tuple[str, Any, Any],
            type_repr,
        )
        self._declare_symbol(name, type_repr)
        return None

    def tff_type(self, items):
        if len(items) == 1:
            return items[0]
        head = items[0]
        for tail in items[1:]:
            head = ("fun", head, tail)
        return head

    def tff_type_product(self, items):
        if len(items) == 1:
            return items[0]
        return list(items)

    def tff_type_atom(self, items):
        if not items:
            return "$tType"
        if len(items) == 1:
            if isinstance(items[0], (list, tuple)):
                return items[0]
            return str(items[0])
        return items

    def thf_or_formula(self, items):
        return self.fof_or_formula(items)

    def thf_and_formula(self, items):
        return self.fof_and_formula(items)

    def thf_app(self, items):
        left, right = items
        return self._apply_expr(self._as_expr(left), self._as_expr(right))

    def thf_lambda(self, items):
        vars_list, body = items
        result = body
        for var in reversed(vars_list):
            result = smt.Lambda([var], result)
        return result

    def _func(self, name: str, arity: int) -> smt.FuncDeclRef:
        key = (name, arity)
        fn = self.funcs.get(key)
        if fn is None:
            sig = self.func_sigs.get(name)
            if sig is not None:
                doms, rng = sig
                if len(doms) != arity:
                    doms = [self.sort] * arity
                    rng = self.sort
                fn = smt.Function(name, *doms, rng)
            else:
                fn = smt.Function(name, *([self.sort] * arity), self.sort)
            self.funcs[key] = fn
        return fn

    def _pred(self, name: str, arity: int) -> smt.FuncDeclRef | smt.BoolRef:
        key = (name, arity)
        fn = self.funcs.get(key)
        if fn is not None and fn.range() == smt.BoolSort():
            return fn
        pred = self.preds.get(key)
        if pred is None:
            if arity == 0:
                pred = smt.Bool(name)
            else:
                pred = smt.Function(name, *([self.sort] * arity), smt.BoolSort())
            self.preds[key] = pred
        return pred

    def _declare_symbol(
        self,
        name: str,
        type_repr: str | list[Any] | tuple[str, Any, Any],
    ):
        if isinstance(type_repr, list) and len(type_repr) == 1:
            type_repr = type_repr[0]
        if type_repr == "$tType":
            sort = self._get_sort(name)
            self.sorts[name] = sort
            return sort
        if isinstance(type_repr, tuple) and type_repr[0] == "fun":
            sig = self._type_repr_to_sort(type_repr)
            assert isinstance(sig, tuple)
            doms, rng = sig
            doms = list(doms)
            rng = rng if rng is not None else self.sort
            self.func_sigs[name] = (doms, rng)
            if not self.thf_mode:
                fn = smt.Function(name, *doms, rng)
                self.funcs[(name, len(doms))] = fn
                return fn
            sort = self._function_sort_from_sig((doms, rng))
            const = smt.Const(name, sort)
            self.consts[name] = const
            return const
        sort = self._type_repr_to_sort(type_repr)
        if isinstance(sort, (list, tuple)):
            sort = self.sort
        if sort is None:
            sort = self.sort
        const = smt.Const(name, sort)
        self.const_sorts[name] = sort
        self.consts[name] = const
        return const

    def _type_repr_to_sort(
        self,
        type_repr: str | list[Any] | tuple[str, Any, Any],
    ) -> (
        smt.SortRef
        | None
        | tuple[list[smt.SortRef], Optional[smt.SortRef]]
        | list[smt.SortRef]
    ):
        if isinstance(type_repr, list) and len(type_repr) == 1:
            type_repr = type_repr[0]
        if isinstance(type_repr, tuple) and type_repr[0] == "fun":
            dom = type_repr[1]
            rng = type_repr[2]
            dom_sorts = self._type_repr_to_sort(dom)
            if not isinstance(dom_sorts, list):
                dom_sorts = [dom_sorts]
            dom_sorts = [d if d is not None else self.sort for d in dom_sorts]
            rng_sort = self._type_repr_to_sort(rng)
            if isinstance(rng_sort, tuple):
                rng_doms, rng_rng = rng_sort
                dom_sorts.extend(rng_doms)
                rng_sort = rng_rng
            return (
                cast(list[smt.SortRef], dom_sorts),
                cast(Optional[smt.SortRef], rng_sort),
            )
        if isinstance(type_repr, list):
            return [
                cast(smt.SortRef, self._type_repr_to_sort(cast(Any, t)))
                for t in type_repr
            ]
        if isinstance(type_repr, str):
            if type_repr == "$o":
                return smt.BoolSort()
            if type_repr == "$tType":
                return None
            return self._get_sort(type_repr)
        return self.sort

    def _term_name(self, term) -> str:
        if isinstance(term, smt.ExprRef):
            return term.decl().name()
        return str(term)

    def _as_var(self, value) -> smt.ExprRef:
        if isinstance(value, smt.ExprRef):
            return value
        return self.var([value])

    def _get_sort(self, name: str) -> smt.SortRef:
        sort = self.sorts.get(name)
        if sort is None:
            sort = smt.DeclareSort(name)
            self.sorts[name] = sort
        return sort

    def _function_sort_from_sig(
        self, sig: tuple[list[smt.SortRef], Optional[smt.SortRef]]
    ):
        doms, rng = sig
        result = rng if rng is not None else self.sort
        for dom in reversed(doms):
            result = smt.ArraySort(dom, result)
        return result

    def _as_expr(self, value) -> smt.ExprRef:
        if isinstance(value, smt.ExprRef):
            return value
        return smt.Const(str(value), self.sort)

    def _apply_expr(self, head: smt.ExprRef, arg: smt.ExprRef) -> smt.ExprRef:
        if isinstance(head.sort(), smt.ArraySortRef):
            return smt.Select(head, arg)
        return head(arg)


def _has_rule(tree: lark.Tree, name: str) -> bool:
    if isinstance(tree, lark.Tree):
        if tree.data == name:
            return True
        return any(_has_rule(child, name) for child in tree.children)
    return False


def to_z3(tree: lark.Tree, sort: smt.SortRef | None = None) -> list[TPTPFormulaEntry]:
    """
    Transform a TPTP parse tree into Z3 expressions.

    >>> import kdrag.parsers.tptp as tptp
    >>> tree = tptp.fof_parser.parse("fof(a,axiom, p(a) ).")
    >>> entries = tptp.to_z3(tree)
    >>> entries[0].name
    'a'
    >>> entries[0].role
    <FormulaRole.AXIOM: 'axiom'>
    >>> entries[0].formula
    p(a)
    """
    thf_mode = _has_rule(tree, "thf")
    return TPTPTransformer(sort=sort, thf_mode=thf_mode).transform(tree)
