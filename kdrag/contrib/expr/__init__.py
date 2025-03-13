from dataclasses import dataclass


@dataclass
class Context:
    counter = 0


_main_ctx = Context()


def main_ctx():
    return _main_ctx


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
    """ """
    return Function(name, sort, ctx=ctx)()


def Consts(names: str, sort: SortRef) -> list[ExprRef]:
    return [Const(name, sort, ctx=sort.ctx) for name in names.split()]


def FreshConst(sort: SortRef, prefix="c"):
    return Const(prefix + "!" + str(sort.ctx.counter), sort)
