"""
A pure python implementation of an AST for expressions.
"""

from dataclasses import dataclass, field
from typing import NamedTuple
import enum
import kdrag.smt as smt


class Kind(enum.Enum):
    SORT = 0
    DECL = 1
    APP = 2
    VAR = 3


class AstNode(NamedTuple):
    kind: Kind
    children: tuple
    hash: int

    def __hash__(self):
        return self.hash

    def __eq__(self, other):
        return self is other

    @staticmethod
    def create(kind: Kind, children: tuple) -> "AstNode":
        _hash = hash((kind, children))
        return AstNode(kind=kind, children=children, hash=_hash)


@dataclass
class AstRef:
    ctx: "Context"
    ast: AstNode

    def eq(self, other):
        return self.ast is other.ast

    def get_id(self):
        return id(self.ast)


class SortRef(AstRef):
    def __repr__(self):
        assert self.ast.kind == Kind.SORT
        return self.ast.children[0]


class FuncDeclRef(AstRef):
    def name(self):
        assert self.ast.kind == Kind.DECL
        return self.ast.children[0]

    def domain(self, i: int) -> SortRef:
        assert self.ast.kind == Kind.DECL
        return self.ast.children[i + 1]

    def range(self) -> SortRef:
        assert self.ast.kind == Kind.DECL
        return SortRef(self.ctx, self.ast.children[-1])

    def __call__(self, *args: "ExprRef") -> "ExprRef":
        assert len(args) == len(self.ast.children) - 2
        children = (self.ast,) + tuple(arg.ast for arg in args)
        app_ast = self.ctx.hashcons(Kind.APP, children)
        return ExprRef(self.ctx, app_ast)

    def __repr__(self):
        return self.ast.children[0]


class ExprRef(AstRef):
    def decl(self):
        assert self.ast.kind == Kind.APP
        return FuncDeclRef(self.ctx, self.ast.children[0])

    def arg(self, i: int) -> "ExprRef":
        assert self.ast.kind == Kind.APP
        return ExprRef(self.ctx, self.ast.children[i + 1])

    def children(self):
        assert self.ast.kind == Kind.APP
        return [ExprRef(self.ctx, c) for c in self.ast.children[1:]]

    def __add__(self, other):
        assert self.ctx is other.ctx
        return self.ctx.Function("+", self.sort(), self.sort(), self.sort())(
            self, other
        )

    def sort(self) -> SortRef:
        return self.decl().range()

    def __eq__(self, other) -> "ExprRef":  # type: ignore
        assert self.ctx is other.ctx
        return self.ctx.Function("=", self.sort(), self.sort(), self.ctx.BoolSort())(
            self, other
        )

    def __repr__(self):
        if self.ast.kind == Kind.APP:
            decl, children = self.decl(), self.children()
            if len(children) == 0:
                return decl.name()
            else:
                args = " ".join(repr(c) for c in children)
                return f"({decl.name()} {args})"
                # args = ", ".join(repr(self.arg(i)) for i in range(len(self.children())))
                # return f"{decl.name()}({args})"
        else:
            return "<invalid ExprRef>"


@dataclass
class Context:
    """
    >>> ctx = Context()
    >>> s1 = ctx.DeclareSort("S")
    >>> s2 = ctx.DeclareSort("S")
    >>> s1.eq(s2)
    True
    >>> f = ctx.Function("f", s1, ctx.BoolSort())
    >>> x = ctx.Const("x", s1)
    >>> f(x) == ctx.BoolVal(True)
    (= (f x) true)
    >>> ctx.FreshConst(s1, prefix="foo")
    foo!0


    """

    counter = 0
    table: dict = field(default_factory=dict)

    def hashcons(self, kind: Kind, children: tuple) -> AstNode:
        key = (kind, children)
        n = self.table.get(key)
        if n is None:
            n = AstNode.create(kind, children)
            self.table[key] = n
        return n

    def DeclareSort(self, name: str) -> "SortRef":
        node = self.hashcons(Kind.SORT, (name,))
        return SortRef(ctx=self, ast=node)

    def BoolVal(self, value: bool) -> "ExprRef":
        return self.Const("true" if value else "false", self.BoolSort())

    def IntVal(self, value: int) -> "ExprRef":
        return self.Const(str(value), self.IntSort())

    def translate(self, expr: smt.AstRef | AstRef) -> AstRef:
        if isinstance(expr, AstRef):
            if expr.ctx is self:
                return expr
            else:
                raise NotImplementedError("Cross-context translation not implemented")
        elif isinstance(expr, smt.AstRef):
            raise NotImplementedError("Translation from smt.AstRef not implemented")
        else:
            raise TypeError(f"Cannot translate from type {type(expr)}")

    # Actually these don't have to be under ctx, since ctx can be inferred
    def Function(self, name: str, *sig: "SortRef") -> "FuncDeclRef":
        return FuncDeclRef(
            ctx=self,
            ast=self.hashcons(
                Kind.DECL,
                (name,) + tuple(s.ast for s in sig),
            ),
        )

    def IntSort(self) -> "SortRef":
        return self.DeclareSort("Int")

    def BoolSort(self) -> "SortRef":
        return self.DeclareSort("Bool")

    def Const(self, name: str, sort: SortRef) -> "ExprRef":
        func = self.Function(name, sort)
        return func()  # no args

    def Consts(self, names: str, sort: SortRef) -> list["ExprRef"]:
        return [self.Const(name, sort) for name in names.split()]

    def FreshConst(self, sort: SortRef, prefix="c") -> "ExprRef":
        name = f"{prefix}!{self.counter}"
        self.counter += 1
        return self.Const(name, sort)


_main_ctx = Context()


def main_ctx():
    return _main_ctx


"""
@dataclass
class AstRef:
    ctx: Context

    def eq(self, other):
        return self is other

    def get_id(self):
        return id(self)


@dataclass
class SortRef(AstRef):
    _kind: object
    _name: str

    def kind(self):
        return self._kind

    def name(self):
        return self._name


@dataclass
class TypeVarRef(AstRef):
    pass


@dataclass
class FuncDeclRef(AstRef):
    _name: str
    _domain: tuple[SortRef, ...]
    _range: SortRef

    def name(self):
        return self._name

    def arity(self):
        return len(self._domain)

    def domain(self, i):
        return self._domain[i]

    def range(self):
        return self._range

    def __call__(self, *args):
        assert len(args) == len(self._domain)
        return ExprRef(ctx=self.ctx, _decl=self, _args=args)

    # params. huh


def Function(name, *sig, ctx=None):
    assert len(sig) > 0
    if ctx is None:
        ctx = main_ctx()
    return FuncDeclRef(ctx, name, sig[:-1], sig[-1])


@dataclass
class ExprRef(AstRef):
    _decl: FuncDeclRef
    _args: tuple[AstRef, ...]

    def arg(self, i):
        return self._args[i]

    def children(self):
        return list(self._args)

    def decl(self):
        return self._decl

    def num_args(self):
        return len(self._args)

    def _sort(self):
        return self._decl.range()

    def __eq__(self, other):
        raise NotImplementedError

    def __ne__(self, other):
        raise NotImplementedError


def Const(name: str, sort: SortRef, ctx=None) -> ExprRef:
    return Function(name, sort, ctx=ctx)()


def Consts(names: str, sort: SortRef) -> list[ExprRef]:
    return [Const(name, sort, ctx=sort.ctx) for name in names.split()]


def FreshConst(sort: SortRef, prefix="c"):
    return Const(prefix + "!" + str(sort.ctx.counter), sort)
"""
