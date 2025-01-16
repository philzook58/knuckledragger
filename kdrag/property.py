from typing import Optional
import kdrag as kd
from . import smt


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
    >>> obvious.register(R, kd.lemma(smt.ForAll([x(R)], x(R) == x(R))))
    """

    def __init__(self, f):
        self.wrapped = f
        self.data = {}

    def __call__(self, *args) -> kd.Proof:
        return self.data[args]

    def __getitem__(self, *args) -> kd.Proof:
        return self.data[args]

    def get(self, *args) -> Optional[kd.Proof]:
        return self.data.get(args)

    def lemma(self, *args, **kwargs):
        return self.register(*args, kd.kernel.lemma(self.wrapped(*args), **kwargs))

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


@GenericProof
def comm(f: smt.FuncDeclRef):
    T = f.domain(0)
    x, y = smt.Consts("x y", T)
    return kd.QForAll([x, y], f(x, y) == f(y, x))


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
