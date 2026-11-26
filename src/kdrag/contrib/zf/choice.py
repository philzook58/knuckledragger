"""
The axiom of choice (Halmos §15).

Halmos: the Cartesian product of a nonempty family of nonempty sets is
nonempty. Equivalently, as he goes on to use it, every collection C of
nonempty sets has a choice function: a function f on C with f(A) ∈ A for
every A ∈ C. This is the third axiom of contrib.zf, after infinity and
substitution. Only `choice` and `zorn` may use it.
"""

from kdrag import Theorem, axiom, define
from kdrag.smt import And, Consts, Exists, ForAll, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, pow, sing
from kdrag.contrib.zf.fun import app, elem_sub, is_func

A, C, X, f = Consts("A C X f", ZFSet)

choice_ax = axiom(
    ForAll(
        C,
        Not(elem(zf.emp, C)),
        Exists(f, And(is_func(f, C, bigunion(C)), ForAll(A, elem(A, C), elem(app(f, A), A)))),
    )
)

# f chooses an element from every nonempty subset of X.
is_choice_on = define("is_choice_on", [f, X], ForAll(A, A <= X, A != zf.emp, elem(app(f, A), A)))


@Theorem(ForAll(X, Exists(f, is_choice_on(f, X))))
def exists_choice_on(l):
    """Halmos: there is a choice function for the nonempty subsets of X, by the
    axiom applied to P(X) − {∅}."""
    X = l.fix()
    Cx = pow(X) - sing(zf.emp)
    l.have(Not(elem(zf.emp, Cx)), by=[elem_sub, zf.elem_sing])
    l.have(
        Exists(f, And(is_func(f, Cx, bigunion(Cx)), ForAll(A, elem(A, Cx), elem(app(f, A), A)))),
        by=[choice_ax(Cx)],
    )
    f0, _ = l.obtain(-1)
    l.exists(f0)
    l.unfold(is_choice_on)
    A0 = l.fix()
    l.intros()
    l.auto(by=[elem_sub(A0, pow(X), sing(zf.emp)), zf.elem_sing, zf.elem_pow, le.defn])
