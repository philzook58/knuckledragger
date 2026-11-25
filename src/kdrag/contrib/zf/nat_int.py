"""
The von Neumann naturals and z3's built-in integers.

`from_int(i)` is the natural with i elements: ∅ for i ≤ 0 and succ(from_int(i - 1))
otherwise. It is a recursive HOL definition on Int, which kdrag accepts without
a termination check; it terminates because i decreases while positive. z3 can
evaluate it on numerals.

`has_int(x, i)` relates a natural x to the integer counting it, like `has_lim`:
a relation, not a total function. Curried in x it is a class, so omega induction
proves facts about it; `from_int` facts go by induction on Int. There is no
`to_int`: the recursion theorem only builds functions into sets, and Int is not
one.
"""

import kdrag as kd
from kdrag import Theorem, define
from kdrag.smt import (
    And,
    Consts,
    Exists,
    ForAll,
    Function,
    If,
    Implies,
    Ints,
    IntSort,
)
import kdrag.theories.int as int_
from kdrag.theories.zf.zf import ZFSet, elem, succ, zero
from kdrag.contrib.zf.nat import (
    induct_omega,
    omega,
    omega_succ,
    omega_zero,
    succ_inj,
    succ_ne_zero,
    two,
)
from kdrag.contrib.zf.arith import add, add_succ, add_zero

x, y = Consts("x y", ZFSet)
i, j = Ints("i j")

# Declared first so the body can call it, as theories.nat does for its Nat.
from_int = Function("zf.from_int", IntSort(), ZFSet)
from_int = define("zf.from_int", [i], If(i <= 0, zero, succ(from_int(i - 1))))
has_int = define("has_int", [x, i], And(i >= 0, from_int(i) == x))


def induct_int(i: kd.smt.ExprRef, P: kd.smt.QuantifierRef) -> kd.Proof:
    """`using=` hook: `l.induct(i, using=induct_int)` leaves P(0), the step, and i ≥ 0.

    Built from the single axiom behind `theories.int.induct_nat_ax`, so it adds
    no fresh axiom per use, and beta-reduced as `nat.induct_omega` is."""
    n = kd.smt.FreshConst(kd.smt.IntSort(), prefix="n")
    thm = kd.rewrite.beta(
        Implies(
            And(P[0], ForAll(n, Implies(And(n >= 0, P[n]), P[n + 1])), i >= 0), P[i]
        )
    )
    assert isinstance(thm, kd.smt.BoolRef)
    return kd.prove(thm, by=[int_.induct_nat_ax(P)])


from_int_zero = kd.prove(from_int(0) == zero, by=[from_int.defn])
from_int_succ = kd.prove(
    ForAll(i, i >= 0, from_int(i + 1) == succ(from_int(i))), by=[from_int.defn]
)

# z3 evaluates from_int on numerals.
from_int_two = kd.prove(from_int(2) == two, by=[from_int.defn])


@Theorem(ForAll(i, i >= 0, elem(from_int(i), omega)))
def from_int_elem_omega(l):
    i = l.fix()
    l.intro()
    l.induct(i, using=induct_int)
    l.auto(by=[from_int_zero, omega_zero])
    n = l.fix()
    l.intros()
    l.auto(by=[from_int_succ(n), omega_succ])
    l.auto()


@Theorem(ForAll(i, i >= 0, ForAll(j, j >= 0, from_int(i) == from_int(j), i == j)))
def from_int_inj_at(l):
    """Induction on i, for every j at once."""
    i = l.fix()
    l.intro()
    l.induct(i, using=induct_int)
    # 0: from_int(j) = ∅ forces j = 0, since a successor is never ∅.
    j = l.fix()
    l.intros()
    l.auto(by=[from_int_zero, from_int_succ(j - 1), succ_ne_zero(from_int(j - 1))])
    # n + 1: j = 0 is impossible, and j = k + 1 reduces to n = k by Peano V.
    n = l.fix()
    l.intros()
    j = l.fix()
    l.intros()
    l.have(j > 0, by=[from_int_zero, from_int_succ(n), succ_ne_zero(from_int(n))])
    l.have(
        from_int(n) == from_int(j - 1),
        by=[
            from_int_succ(n),
            from_int_succ(j - 1),
            succ_inj(from_int(n), from_int(j - 1)),
            from_int_elem_omega(n),
            from_int_elem_omega(j - 1),
        ],
    )
    l.auto()
    l.auto()


from_int_inj = kd.prove(
    ForAll([i, j], i >= 0, j >= 0, from_int(i) == from_int(j), i == j),
    by=[from_int_inj_at],
)


@Theorem(ForAll(x, elem(x, omega), Exists(i, has_int(x, i))))
def exists_has_int(l):
    """Every natural has an integer, by omega induction on the class λx. ∃i. has_int(x, i)."""
    x = l.fix()
    l.intro()
    l.induct(x, using=induct_omega)
    l.exists(kd.smt.IntVal(0))
    l.auto(by=[has_int.defn, from_int_zero])
    l.fix()
    l.intros()
    i0 = l.obtain(-1)[0]
    l.exists(i0 + 1)
    l.auto(by=[has_int.defn, from_int_succ(i0)])
    l.auto()


has_int_unique = kd.prove(
    ForAll([x, i, j], has_int(x, i), has_int(x, j), i == j),
    by=[has_int.defn, from_int_inj],
)
has_int_elem_omega = kd.prove(
    ForAll([x, i], has_int(x, i), elem(x, omega)),
    by=[has_int.defn, from_int_elem_omega],
)
has_int_zero = kd.prove(has_int(zero, 0), by=[has_int.defn, from_int_zero])
has_int_succ = kd.prove(
    ForAll([x, i], has_int(x, i), has_int(succ(x), i + 1)),
    by=[has_int.defn, from_int_succ],
)


@Theorem(ForAll([x, y, i, j], has_int(x, i), has_int(y, j), has_int(add(x, y), i + j)))
def has_int_add(l):
    """Addition on ω agrees with addition on Int."""
    x, y, i, j = l.fixes()
    l.intros()
    l.have(elem(x, omega), by=[has_int_elem_omega(x, i)])
    l.have(y == from_int(j), by=[has_int.defn])
    l.have(j >= 0, by=[has_int.defn])
    l.have(
        ForAll(j, j >= 0, has_int(add(x, from_int(j)), i + j)),
    )
    j1 = l.fix()
    l.intro()
    l.induct(j1, using=induct_int)
    l.auto(by=[has_int.defn, from_int_zero, add_zero(x)])
    n = l.fix()
    l.intros()
    l.auto(
        by=[
            from_int_succ(n),
            add_succ(x, from_int(n)),
            from_int_elem_omega(n),
            has_int_succ(add(x, from_int(n)), i + n),
        ]
    )
    l.auto()
    l.auto()
