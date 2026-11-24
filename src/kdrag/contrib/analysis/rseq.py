"""Sequence-limit arithmetic and automation.

Build on the reviewed sequence theory without redefining its sequences or lim.
"""

from typing import Optional

from kdrag import FreshVar, Proof, Theorem, prove
import kdrag.smt as smt
from kdrag.smt import (
    And,
    BoolRef,
    Eq,
    ExprRef,
    ForAll,
    If,
    Implies,
    Lambda,
    RealSort,
    RealVal,
    Reals,
    is_add,
    is_app,
    is_div,
    is_implies,
    is_mul,
    is_neg,
    is_power,
    is_select,
    is_sub,
)
from kdrag.utils import alpha_eq, occurs
import kdrag.theories.real as real
from kdrag.theories.real.rseq import (
    RSeq,
    a,
    b,
    x,
    y,
    r,
    k,
    n,
    add,
    const,
    div,
    div_decomp,
    eventually,
    eventually_and,
    eventually_mono,
    eventually_near,
    has_lim,
    has_lim_add,
    has_lim_const,
    has_lim_iff,
    has_lim_inv,
    has_lim_neg,
    has_lim_squeeze,
    has_lim_sub,
    mul,
    near,
    neg,
    shift,
    smul,
    sub,
)

da, db, X, Y, B, eta, eps = Reals("da db X Y B eta eps")


@Theorem(
    ForAll(
        [a, b, x],
        has_lim(a, x),
        ForAll(n, n >= 0, a[n] == b[n]),
        has_lim(b, x),
    )
)
def has_lim_congr_nonneg(l):
    """Sequences that agree at nonnegative indices have the same limits."""
    a, b, x = l.fixes()
    l.intros()
    l.auto(by=[has_lim_squeeze(a, b, a, x)])


@Theorem(ForAll([a, x, k], has_lim(a, x), has_lim(shift(a, k), x)))
def has_lim_shift(l):
    """Translating the index by an integer preserves the limit."""
    a, x, k = l.fixes()
    l.unfold(has_lim)
    tends = l.intro()
    l.unfold(shift)
    eps = l.fix()
    positive = l.intro()
    N, close = l.obtain(l.specialize(tends, eps, positive))
    l.exists(N + k)
    j = l.fix()
    l.intro()
    l.specialize(close, j - k)
    l.auto()


start = smt.Int("start")
center, radius = Reals("center radius")


@Theorem(
    ForAll(
        [a, x, center, radius, start],
        has_lim(a, x),
        ForAll(n, n >= start, real.abs(a[n] - center) <= radius),
        real.abs(x - center) <= radius,
    )
)
def abs_sub_le_of_has_lim(l):
    """A closed interval containing the tail also contains its limit."""
    a, x, center, radius, start = l.fixes()
    l.rw(has_lim_iff(a, x))
    l.unfold(eventually)
    l.beta()
    limit, bound = l.intros()
    l.contra()
    gap = real.abs(x - center) - radius
    positive = l.have(gap > 0, by=[])
    cutoff, near = l.obtain(l.specialize(limit, gap, positive))
    index = If(cutoff >= start, cutoff + 1, start)
    beyond = l.have(index > cutoff, by=[])
    l.specialize(near, index, beyond)
    after_start = l.have(index >= start, by=[])
    l.specialize(bound, index, after_start)
    l.auto(by=[real.abs_triangle(x, center, a[index]), real.abs_neg(a[index] - x)])


@Theorem(
    ForAll(
        [r, a, x],
        has_lim(a, x),
        has_lim(smul(r, a), r * x),
    ),
)
def has_lim_smul(l):
    r, a, x = l.fixes()
    l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    # A positive denominator handles zero and nonzero scalars uniformly.
    eta = eps / (real.abs(r) + 1)
    l.have(eta > 0, by=[real.abs_pos(r)])
    l.have(eventually(near(a, x, eta)), by=[eventually_near(a, x, eta)])
    # Pointwise: |r a[m] - r x| = |r| |a[m] - x| < eps.
    l.have(ForAll([n], real.abs(a[n] - x) < eta, real.abs(smul(r, a)[n] - r * x) < eps))
    l.unfold(smul)
    l.beta()
    m = l.fix()
    l.intros()
    l.have(real.abs(r) * eta < eps, by=[real.abs_pos(r)])
    l.have(
        real.abs(r * a[m] - r * x) == real.abs(r) * real.abs(a[m] - x),
        by=[real.abs_mul(r, a[m] - x)],
    )
    l.auto(by=[real.abs_pos(r)])
    l.auto(by=[eventually_mono(near(a, x, eta), near(smul(r, a), r * x, eps))])


@Theorem(
    ForAll(
        [da, db, X, Y, eta, eps],
        And(0 <= da, da < eta, 0 <= db, db < eta, eta <= 1, 0 <= X, 0 <= Y),
        2 * eta * (X + Y + 1) <= eps,
        da * db + Y * da + X * db < eps,
    )
)
def mul_error_lt(l):
    """Errors below eta <= 1 keep the product error da db + Y da + X db below eps."""
    l.fixes()
    l.intros()
    l.intros()
    l.auto()


@Theorem(
    ForAll(
        [da, db, X, Y, B, eps],
        And(0 <= da, 0 <= db, 0 <= X, 0 < Y, Y / 2 < B),
        da < eps * Y / 4,
        db < eps * Y * Y / (4 * (X + 1)),
        da / B + X * (db / (B * Y)) < eps,
    )
)
def div_error_lt(l):
    """Errors da, db with |b| = B > Y/2 keep the quotient error below eps."""
    l.fixes()
    l.intros(), l.intros(), l.intros()
    l.auto()


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        has_lim(a * b, x * y),
    ),
)
def has_lim_mul(l):
    a, b, x, y = l.fixes()
    l.intros(), l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    # Keep both errors below one and small enough for the product estimate.
    eta = real.min(1, eps / (2 * (real.abs(x) + real.abs(y) + 1)))
    l.have(eta > 0, by=[real.abs_pos(x), real.abs_pos(y), real.min.defn])
    Pa, Pb = near(a, x, eta), near(b, y, eta)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, eta)])
    l.have(eventually(Pb), by=[eventually_near(b, y, eta)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: expand a[m] b[m] - x y and bound each term.
    l.have(
        ForAll(
            [n],
            And(real.abs(a[n] - x) < eta, real.abs(b[n] - y) < eta),
            real.abs((a * b)[n] - x * y) < eps,
        )
    )
    l.unfold(mul)
    l.beta()
    m = l.fix()
    l.intros()
    l.have(
        And(eta <= 1, 2 * eta * (real.abs(x) + real.abs(y) + 1) <= eps),
        by=[real.abs_pos(x), real.abs_pos(y), real.min.defn],
    )
    u, v = a[m] - x, b[m] - y
    da, db = real.abs(u), real.abs(v)
    error_bound = da * db + real.abs(y) * da + real.abs(x) * db
    l.have(a[m] * b[m] - x * y == u * v + y * u + x * v, by=[])
    l.have(
        real.abs(a[m] * b[m] - x * y) <= error_bound,
        by=[
            real.abs_add(u * v + y * u, x * v),
            real.abs_add(u * v, y * u),
            real.abs_mul(u, v),
            real.abs_mul(y, u),
            real.abs_mul(x, v),
        ],
    )
    l.have(
        error_bound < eps,
        by=[
            mul_error_lt(da, db, real.abs(x), real.abs(y), eta, eps),
            real.abs_pos(u),
            real.abs_pos(v),
            real.abs_pos(x),
            real.abs_pos(y),
        ],
    )
    l.auto()
    l.auto(by=[eventually_mono(both, near(a * b, x * y, eps))])


@Theorem(
    ForAll([a, b, x, y], has_lim(a, x), has_lim(b, y), y != 0, has_lim(a / b, x / y))
)
def has_lim_div(l):
    a, b, x, y = l.fixes()
    l.intros(), l.intros(), l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    # Keep the denominator away from zero and split the quotient error.
    Y, X = real.abs(y), real.abs(x)
    ea = eps * Y / 4
    eb = real.min(Y / 2, eps * Y * Y / (4 * (X + 1)))
    l.have(Y > 0, by=[real.abs_pos_iff(y)])
    l.have(ea > 0, by=[])
    l.have(eb > 0, by=[real.abs_pos(x), real.min.defn])
    Pa, Pb = near(a, x, ea), near(b, y, eb)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, ea)])
    l.have(eventually(Pb), by=[eventually_near(b, y, eb)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: split a[m]/b[m] - x/y into a numerator and a denominator error.
    l.have(
        ForAll(
            [n],
            And(real.abs(a[n] - x) < ea, real.abs(b[n] - y) < eb),
            real.abs((a / b)[n] - x / y) < eps,
        )
    )
    l.unfold(div)
    l.beta()
    m = l.fix()
    l.intros()

    am, bm = a[m], b[m]
    da, db, B = real.abs(am - x), real.abs(bm - y), real.abs(bm)
    l.have(And(db < Y / 2, db < eps * Y * Y / (4 * (X + 1))), by=[real.min.defn])
    l.have(real.abs(y - bm) == db, by=[real.abs_neg(bm - y)])
    l.have(Y <= db + B, by=[real.abs_triangle(y, RealVal(0), bm)])
    l.have(B > Y / 2, by=[])
    l.have(bm != 0, by=[real.abs_pos_iff(bm)])
    t1 = (am - x) / bm
    t2 = x * ((y - bm) / (bm * y))
    decomp = l.have(am / bm - x / y == t1 + t2, by=[div_decomp(am, bm, x, y)])
    l.have(real.abs(t1) == da / B, by=[real.abs_div(am - x, bm)])
    q = (y - bm) / (bm * y)
    l.have(real.abs(bm * y) == B * Y, by=[real.abs_mul(bm, y)])
    l.have(real.abs(q) == db / (B * Y), by=[real.abs_div(y - bm, bm * y)])
    l.have(real.abs(t2) == X * (db / (B * Y)), by=[real.abs_mul(x, q)])
    # The nonlinear error budget, proved once in div_error_lt.
    l.have(
        da / B + X * (db / (B * Y)) < eps,
        by=[
            div_error_lt(da, db, X, Y, B, eps),
            real.abs_pos(am - x),
            real.abs_pos(bm - y),
            real.abs_pos(x),
        ],
    )
    bound = l.have(real.abs(t1 + t2) < eps, by=[real.abs_add(t1, t2)])
    # Discharge congruence with just the equality and the scalar bound.
    result = real.abs(am / bm - x / y) < eps
    l.auto(by=[prove(Implies(And(decomp, bound), result))])
    l.auto(by=[eventually_mono(both, near(a / b, x / y, eps))])


# Limit rule for each sequence operation. A rule's binders are the operation's
# arguments in order, followed by the limits of its sequence arguments.
lim_rules = {
    neg: has_lim_neg,
    add: has_lim_add,
    sub: has_lim_sub,
    mul: has_lim_mul,
    div: has_lim_div,
    smul: has_lim_smul,
    const: has_lim_const,
}

# Known limits `has_lim(seq, value)` of particular sequences, used for atoms.
lim_facts = [has_lim_inv]

# z3 arithmetic on reals, as binary sequence operations folded over arguments.
_arith_ops = [(is_add, add), (is_sub, sub), (is_mul, mul), (is_div, div)]


def _known_lim(t: ExprRef) -> Optional[Proof]:
    return next((f for f in lim_facts if alpha_eq(f.thm.arg(0), t)), None)


def _nat_exponent(p: ExprRef) -> Optional[int]:
    if isinstance(p, smt.IntNumRef):
        k = p.as_long()
    elif isinstance(p, smt.RatNumRef) and p.denominator_as_long() == 1:
        k = p.numerator_as_long()
    else:
        return None
    return k if k >= 1 else None


def _to_seq(e: ExprRef, n: ExprRef) -> ExprRef:
    """A sequence term equal to Lambda(n, e), built from the sequence operations."""
    if not occurs(n, e):
        return const(e)
    if _known_lim(Lambda([n], e)) is not None:
        return Lambda([n], e)
    if is_select(e) and e.arg(1).eq(n) and not occurs(n, e.arg(0)):
        return e.arg(0)  # a[n] is the sequence a
    cs = e.children()
    for is_op, op in _arith_ops:
        if is_op(e):
            acc = _to_seq(cs[0], n)
            for c in cs[1:]:
                acc = op(acc, _to_seq(c, n))
            return acc
    if is_neg(e):
        return neg(_to_seq(cs[0], n))
    if is_power(e) and (p := _nat_exponent(cs[1])) is not None:
        base = _to_seq(cs[0], n)
        acc = base
        for _ in range(p - 1):
            acc = mul(acc, base)
        return acc
    return Lambda([n], e)  # Anything else is an atom.


def lim_lemma(e: ExprRef, n: Optional[ExprRef] = None) -> Proof:
    """
    Prove the limit of a sequence expression from limits of its atoms.

    Recurse through the sequence operations in `lim_rules`. Atoms with a
    limit in `lim_facts` use it. Every other atom is assumed to converge to a
    fresh limit, in order of first occurrence. Side conditions of the rules,
    such as a nonzero denominator limit, become premises.

    With an index `n`, `e` is a real term in `n` and the result is about
    `Lambda(n, e)`.

    >>> a, b = smt.Consts("a b", RSeq)
    >>> lim_lemma(a * b + smul(2, a))
    |= ForAll([L!..., L!...],
           Implies(And(has_lim(a, L!...), has_lim(b, L!...)),
                   has_lim(... L!...*L!... + 2*L!...)))
    >>> lim_lemma(2 * a[n] + RealVal(1) / n, n)
    |= ForAll(L!...,
           Implies(has_lim(a, L!...),
                   has_lim(Lambda(n, 2*a[n] + 1/ToReal(n)), 2*L!... + 0)))
    """
    target, eqs = e, []
    if n is not None:
        target, e = Lambda([n], e), _to_seq(e, n)
        defns = [f.defn for f in (add, const, div, mul, neg, sub)]
        eqs = [prove(Eq(target, e), by=defns)]
    leaves: dict[ExprRef, ExprRef] = {}
    lemmas: list[Proof] = []
    hyps: list[BoolRef] = []

    def worker(t: ExprRef) -> ExprRef:
        rule = lim_rules.get(t.decl()) if is_app(t) else None
        if rule is None:
            known = _known_lim(t)
            if known is not None:
                lemmas.append(known)
                return known.thm.arg(1)
            # An atom: assume it converges, once per distinct atom.
            if not any(t.eq(u) for u in leaves):
                leaves[t] = FreshVar("L", RealSort())
            return next(y for u, y in leaves.items() if t.eq(u))
        ys = [worker(c) for c in t.children() if c.sort() == RSeq]
        pf = rule(*t.children(), *ys)
        lemmas.append(pf)
        # Premises that are not limits of children are side conditions.
        concl = pf.thm
        while is_implies(concl):
            if concl.arg(0).decl() != has_lim:
                hyps.append(concl.arg(0))
            concl = concl.arg(1)
        return concl.arg(1)

    lim_e = worker(e)
    prems = [has_lim(t, y) for t, y in leaves.items()] + hyps
    concl = has_lim(target, lim_e)
    if prems:
        concl = Implies(prems[0] if len(prems) == 1 else And(prems), concl)
    # Chaining the instantiated lemmas is propositional.
    pf = prove(concl, by=lemmas + eqs)
    return pf.forall(list(leaves.values()))
