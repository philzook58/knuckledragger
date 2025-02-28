"""
Generic properties like associativity, commutativity, idempotence, etc.
"""

from typing import Optional
import kdrag as kd
from . import smt


class TypeClass:
    """
    Subclass this to define a typeclass. The class itself holds a registry of information
    The key can be any valid Python key, but the expected types are smt.ExprRef and smt.FuncDeclRef.
    When you instantiate the class as usual, you hand the key to the constructor and the class will
    look up the information in the registry and populate the fields in the returned instance .
    look up the information in the registry and populate the fields in the returned instance.
    See https://okmij.org/ftp/ML/canonical.html for more on the programmatic approach to typeclasses.

    >>> class Monoid(TypeClass):
    ...     def check(self, T):
    ...         assert isinstance(self.mappend, smt.FuncDeclRef) and self.mappend.arity() == 2
    ...         assert isinstance(self.mempty, smt.ExprRef)
    ...         assert self.mappend.domain(0) == self.mappend.domain(1) == self.mempty.sort() == self.mappend.range()
    ...
    >>> x = smt.Int("x")
    >>> Monoid.register(smt.IntSort(), mappend=(x + x).decl(), mempty=smt.IntVal(0))
    >>> Monoid(smt.IntSort())
    Monoid({'key': (Int,), 'mappend': +, 'mempty': 0})
    """

    # We need to lazily instantiate so different subclasses of TypeClass do not share the same registry.
    _registry = None

    def __init__(self, *L):
        self.key = L
        registry = self.get_registry()
        if L not in registry:
            raise ValueError("Not registered in typeclass", L)
        for k, v in registry[L].items():
            setattr(self, k, v)
        if hasattr(self, "check"):
            self.check(*L)  # type: ignore

    @classmethod
    def get_registry(cls) -> dict:
        if cls._registry is None:
            cls._registry = {}
        return cls._registry

    @classmethod
    def lookup(cls, *L):
        return cls.get_registry()[L]

    """
    @classmethod
    def __contains__(cls, L) -> bool:
        return L in cls.get_registry()
    """

    @classmethod
    def register(cls, *L, **kwargs):
        registry = cls.get_registry()
        if L in registry:
            raise ValueError("Already registered key", L)
        registry[L] = kwargs
        assert cls(*L) is not None  # perform check

    # If we have this stub, pyright complains about overloading
    # def check(self, *L):
    #    pass

    def assert_eq(self, propname, b):
        a = getattr(self, propname)
        if not kd.utils.alpha_eq(a.thm, b):
            raise ValueError(f"Property {propname}, does not match", a, b)

    def __repr__(self):
        return type(self).__name__ + "(" + repr(self.__dict__) + ")"


class GenericProof:
    """
    GenericProof is a dictionary of proofs indexed on meta (python) information.

    Because z3 and hence knuckledragger does not have strong generic support inside its logic,
    we can borrow a bit of python to parametrize theorems over other data or over sorts.

    This has some of the flavor of single dispatch.

    It is similar to an axiom schema is some respects (in usage it takes in python data and outputs a `kd.Proof`) except that one must register
    the theorems as proven by other means.

    It is a way to refer to a collection of similar proofs akin to single entry typeclasses or modules in other theorem proving systems.

    >>> x = lambda T: smt.Const("x", T)
    >>> obvious = GenericProof(lambda T: smt.ForAll([x(T)], x(T) == x(T)) )
    >>> obvious.lemma(smt.IntSort(), by=[])
    >>> R = smt.RealSort()
    >>> obvious.register(R, kd.prove(smt.ForAll([x(R)], x(R) == x(R))))
    """

    def __init__(self, f):
        self.wrapped = f
        self.data = {}

    def __call__(self, *args) -> kd.Proof:
        return self.data[args]

    def __getitem__(self, *args) -> kd.Proof:
        return self.data[args]

    def __contains__(self, *args) -> bool:
        return args in self.data

    def get(self, *args) -> Optional[kd.Proof]:
        return self.data.get(args)

    def lemma(self, *args, **kwargs):
        return self.register(*args, kd.kernel.prove(self.wrapped(*args), **kwargs))

    def register(self, *args):
        args, pf = args[:-1], args[-1]
        if not kd.kernel.is_proof(pf):
            raise ValueError("Not a proof", pf)
        formula = self.wrapped(*args)
        if not kd.utils.alpha_eq(formula, pf.thm):
            raise ValueError("Proof does not match", formula, pf)
        self.data[args] = pf


@GenericProof
def assoc(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y, z = smt.Consts("x y z", T)
    return kd.QForAll([x, y, z], f(x, f(y, z)) == f(f(x, y), z))


x, y, z = smt.Ints("x y z")
assoc.register(
    (x + y).decl(), kd.prove(smt.ForAll([x, y, z], x + (y + z) == (x + y) + z))
)
assoc.register(
    (x * y).decl(), kd.prove(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
)


@GenericProof
def comm(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y = smt.Consts("x y", T)
    return kd.QForAll([x, y], f(x, y) == f(y, x))


comm.register((x + y).decl(), kd.prove(smt.ForAll([x, y], x + y == y + x)))


@GenericProof
def idem(f: smt.FuncDeclRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, x) == x)


@GenericProof
def runit(f: smt.FuncDeclRef, e: smt.ExprRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, e) == x)


@GenericProof
def inv(f: smt.FuncDeclRef, inv: smt.FuncDeclRef, e: smt.ExprRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, inv(x)) == e)


@GenericProof
def symm(R: smt.FuncDeclRef):
    x, y = smt.Consts("x y", R.domain(0))
    return kd.QForAll([x, y], R(x, y) == R(y, x))


@GenericProof
def trans(R: smt.FuncDeclRef):
    x, y, z = smt.Consts("x y z", R.domain(0))
    return kd.QForAll([x, y, z], R(x, y), R(y, z), R(x, z))
