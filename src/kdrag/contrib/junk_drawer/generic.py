import kdrag as kd
import kdrag.smt as smt
from typing import Optional


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

    def assert_eq(self, a, b):
        # a = getattr(self, propname)
        if not kd.utils.alpha_eq(a, b):
            raise ValueError("Property does not match", a, b)

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
    return kd.QForAll([x, y, z], f(f(x, y), z) == f(x, f(y, z)))


x, y, z = smt.Ints("x y z")
assoc.register(
    (x + y).decl(), kd.prove(smt.ForAll([x, y, z], (x + y) + z == x + (y + z)))
)
assoc.register(
    (x * y).decl(), kd.prove(smt.ForAll([x, y, z], (x * y) * z == x * (y * z)))
)


def assoc_norm(e: smt.ExprRef, trace=None) -> smt.ExprRef:
    """

    >>> T = smt.DeclareSort("T")
    >>> x, y, z,w = smt.Ints("x y z w")
    >>> assoc_norm((x + y) + (z + w)).eq(x + (y + (z + w)))
    True
    """
    if smt.is_app(e):
        f = e.decl()
        if f in assoc:
            c = assoc_norm(e.arg(1), trace=trace)  # normalize list tail
            # (a  * b) * c -> a * (b * c)
            todo = [e.arg(0)]
            while todo:
                x = todo.pop()
                if smt.is_app(x) and x.decl() == f:
                    a, b = x.children()
                    if trace is not None:
                        trace.append(assoc[f](a, b, c))
                    todo.append(x.arg(0))
                    todo.append(x.arg(1))
                else:  # x is not f so it can actually be consed onto c.
                    c = f(x, c)
            return c
        else:
            return f(*[assoc_norm(arg) for arg in e.children()])
    else:
        return e


@GenericProof
def comm(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y = smt.Consts("x y", T)
    return kd.QForAll([x, y], f(x, y) == f(y, x))


def comm_norm(e: smt.ExprRef, trace=None) -> smt.ExprRef:
    """
    >>> x,y = smt.Ints("x y")
    >>> assert comm_norm(y + x).eq(x + y)
    """
    if smt.is_app(e):
        f = e.decl()
        args = [comm_norm(arg) for arg in e.children()]
        if f in comm:
            x, y = args
            if x.decl().name() > y.decl().name():  # Todo: This is a bad ordering.
                if trace is not None:
                    trace.append(comm[f](x, y))
                return f(y, x)
            else:
                return f(x, y)
        else:
            return f(*args)
    else:
        return e


comm.register((x + y).decl(), kd.prove(smt.ForAll([x, y], x + y == y + x)))


def assoc_comm(f: smt.FuncDeclRef) -> kd.Proof:
    x, y, z = smt.Consts("x y z", f.domain(0))
    return kd.prove(
        kd.QForAll([x, y, z], f(x, (y, z)) == f(y, f(x, z))), by=[assoc[f], comm[f]]
    )


@GenericProof
def idem(f: smt.FuncDeclRef):
    T = f.domain(0)
    x = smt.Const("x", T)
    return kd.QForAll([x], f(x, x) == x)


a, b = smt.Bools("a b")
idem.register(smt.And(a, a).decl(), kd.prove(smt.ForAll([a], smt.And(a, a) == a)))


def idem_norm(e: smt.ExprRef, trace=None) -> smt.ExprRef:
    """
    >>> idem_norm(smt.And(a, smt.And(a, a)))
    a
    """
    # Maybe this is overwrought. Rewrite on the idem axiom also works.
    if smt.is_app(e):
        f = e.decl()
        args = [idem_norm(arg, trace=trace) for arg in e.children()]
        if f.arity() == 2 and args[0].eq(args[1]) and f in idem:
            if trace is not None:
                trace.append(idem.get(f))
            return args[0]
        else:
            return f(*args)
    else:
        return e


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
