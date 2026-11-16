"""Algebra of real sequence limits."""

from typing import Optional

from kdrag import FreshVar, Proof, Theorem, prove
from kdrag.utils import alpha_eq, occurs
import kdrag.smt as smt
from kdrag.smt import (
    And,
    BoolRef,
    Consts,
    Eq,
    ExprRef,
    ForAll,
    If,
    Implies,
    Int,
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
from kdrag.theories.real import (
    RSeq,
    abs,
    abs_add,
    abs_div,
    abs_mul,
    abs_neg,
    abs_pos,
    abs_pos_iff,
    abs_triangle,
    min,
)
from kdrag.theories.real.seq import (
    add,
    const,
    div,
    eventually,
    eventually_and,
    eventually_mono,
    eventually_of_forall_nonneg,
    eventually_near,
    has_lim,
    has_lim_const,
    has_lim_iff,
    has_lim_inv,
    mul,
    near,
    neg,
    smul,
    sub,
    sub_eq_add_neg,
)


a, b, d = Consts("a b d", RSeq)
x, y, c = Reals("x y c")
u, v, w, z = Reals("u v w z")
n = Int("n")


@Theorem(ForAll([a, y], has_lim(a, y), ForAll(n, n >= 0, a[n] >= 0), y >= 0))
def lim_of_nonneg_seq(l):
    a, y = l.fixes()
    limit, nonneg = l.intros(), l.intros()
    l.unfold(has_lim, at=limit)
    l.contra()
    positive = l.have(-y > 0, by=[])
    cutoff = l.obtain(l.specialize(0, -y, positive))
    m = If(cutoff > 0, cutoff, 0) + 1
    l.specialize(nonneg, m)
    l.auto(by=[abs.defn(a[m] - y)])


@Theorem(
    ForAll(
        [c, a, x],
        has_lim(a, x),
        has_lim(smul(c, a), c * x),
    ),
)
def has_lim_smul(l):
    c, a, x = l.fixes()
    l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    # A positive denominator handles zero and nonzero scalars uniformly.
    eta = eps / (abs(c) + 1)
    l.have(eta > 0, by=[abs_pos(c)])
    l.have(eventually(near(a, x, eta)), by=[eventually_near(a, x, eta)])
    # Pointwise: |c a[m] - c x| = |c| |a[m] - x| < eps.
    l.have(ForAll([n], abs(a[n] - x) < eta, abs(smul(c, a)[n] - c * x) < eps))
    m = l.fix()
    l.intros()
    l.have(abs(c) * eta < eps, by=[abs_pos(c)])
    l.have(c * a[m] - c * x == c * (a[m] - x), by=[])
    l.auto(by=[smul.defn(c, a), abs_mul(c, a[m] - x), abs_pos(c)])
    l.auto(by=[eventually_mono(near(a, x, eta), near(smul(c, a), c * x, eps))])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        has_lim(a + b, x + y),
    ),
)
def has_lim_add(l):
    a, b, x, y = l.fixes()
    l.intros(), l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    # Each sequence contributes half the error budget.
    e = eps / 2
    Pa, Pb = near(a, x, e), near(b, y, e)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, e)])
    l.have(eventually(Pb), by=[eventually_near(b, y, e)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: the triangle inequality.
    l.have(
        ForAll(
            [n],
            And(abs(a[n] - x) < e, abs(b[n] - y) < e),
            abs((a + b)[n] - (x + y)) < eps,
        )
    )
    m = l.fix()
    l.intros()
    l.auto(by=[add.defn(a, b), abs_add(a[m] - x, b[m] - y)])
    l.auto(by=[eventually_mono(both, near(a + b, x + y, eps))])


@Theorem(ForAll([a, x], has_lim(a, x), has_lim(-a, -x)))
def has_lim_neg(l):
    a, x = l.fixes()
    l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    l.have(eventually(near(a, x, eps)), by=[eventually_near(a, x, eps)])
    # Pointwise: |-a[m] - -x| = |a[m] - x|.
    l.have(ForAll([n], abs(a[n] - x) < eps, abs((-a)[n] - -x) < eps))
    l.unfold(neg)
    l.beta()
    m = l.fix()
    l.intros()
    l.auto(by=[abs_neg(a[m] - x)])
    l.auto(by=[eventually_mono(near(a, x, eps), near(-a, -x, eps))])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        has_lim(a - b, x - y),
    ),
)
def has_lim_sub(l):
    a, b, x, y = l.fixes()
    l.rw(sub_eq_add_neg)
    l.auto(by=[has_lim_add(a, -b, x, -y), has_lim_neg(b, y)])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        ForAll(n, n >= 0, a[n] <= b[n]),
        x <= y,
    ),
)
def le_of_has_lim_of_has_lim(l):
    """Limits preserve non-strict inequalities between sequences."""
    a, b, x, y = l.fixes()
    l.auto(
        by=[
            sub.defn(b, a),
            has_lim_sub(b, a, y, x),
            lim_of_nonneg_seq(b - a, y - x),
        ]
    )


@Theorem(ForAll([a, x, c], has_lim(a, x), ForAll(n, n >= 0, a[n] <= c), x <= c))
def le_of_has_lim(l):
    a, x, c = l.fixes()
    l.auto(
        by=[
            le_of_has_lim_of_has_lim(a, const(c), x, c),
            has_lim_const(c),
            const.defn(c),
        ]
    )


@Theorem(ForAll([a, x, c], has_lim(a, x), ForAll(n, n >= 0, c <= a[n]), c <= x))
def ge_of_has_lim(l):
    a, x, c = l.fixes()
    l.auto(
        by=[
            le_of_has_lim_of_has_lim(const(c), a, c, x),
            has_lim_const(c),
            const.defn(c),
        ]
    )


@Theorem(
    ForAll(
        [a, b, d, x],
        has_lim(a, x),
        has_lim(d, x),
        ForAll(n, n >= 0, And(a[n] <= b[n], b[n] <= d[n])),
        has_lim(b, x),
    ),
)
def has_lim_squeeze(l):
    """Squeeze theorem: a sequence trapped between two with limit x has limit x."""
    a, b, d, x = l.fixes()
    l.intros(), l.intros(), l.intros()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intros()
    Pa, Pd = near(a, x, eps), near(d, x, eps)
    between = Lambda([n], And(a[n] <= b[n], b[n] <= d[n]))
    both = Lambda([n], And(Pa[n], Pd[n]))
    trapped = Lambda([n], And(both[n], between[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, eps)])
    l.have(eventually(Pd), by=[eventually_near(d, x, eps)])
    l.have(eventually(between), by=[eventually_of_forall_nonneg(between)])
    l.have(eventually(both), by=[eventually_and(Pa, Pd)])
    l.have(eventually(trapped), by=[eventually_and(both, between)])
    # Pointwise: b[m] lies between a[m] and d[m], both within eps of x.
    l.have(
        ForAll(
            [n],
            And(abs(a[n] - x) < eps, abs(d[n] - x) < eps),
            And(a[n] <= b[n], b[n] <= d[n]),
            abs(b[n] - x) < eps,
        )
    )
    m = l.fix()
    l.intros(), l.intros()
    l.auto(by=[abs.defn(a[m] - x), abs.defn(d[m] - x), abs.defn(b[m] - x)])
    l.auto(by=[eventually_mono(trapped, near(b, x, eps))])


da, db, X, Y, eta, eps = Reals("da db X Y eta eps")


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
    eta = min(1, eps / (2 * (abs(x) + abs(y) + 1)))
    l.have(eta > 0, by=[abs_pos(x), abs_pos(y), min.defn])
    Pa, Pb = near(a, x, eta), near(b, y, eta)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, eta)])
    l.have(eventually(Pb), by=[eventually_near(b, y, eta)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: expand a[m] b[m] - x y and bound each term.
    l.have(
        ForAll(
            [n],
            And(abs(a[n] - x) < eta, abs(b[n] - y) < eta),
            abs((a * b)[n] - x * y) < eps,
        )
    )
    l.unfold(mul)
    l.beta()
    m = l.fix()
    l.intros()
    l.have(
        And(eta <= 1, 2 * eta * (abs(x) + abs(y) + 1) <= eps),
        by=[abs_pos(x), abs_pos(y), min.defn],
    )
    u, v = a[m] - x, b[m] - y
    da, db = abs(u), abs(v)
    error_bound = da * db + abs(y) * da + abs(x) * db
    l.have(a[m] * b[m] - x * y == u * v + y * u + x * v, by=[])
    l.have(
        abs(a[m] * b[m] - x * y) <= error_bound,
        by=[
            abs_add(u * v + y * u, x * v),
            abs_add(u * v, y * u),
            abs_mul(u, v),
            abs_mul(y, u),
            abs_mul(x, v),
        ],
    )
    l.have(
        error_bound < eps,
        by=[
            mul_error_lt(da, db, abs(x), abs(y), eta, eps),
            abs_pos(u),
            abs_pos(v),
            abs_pos(x),
            abs_pos(y),
        ],
    )
    l.auto()
    l.auto(by=[eventually_mono(both, near(a * b, x * y, eps))])


@Theorem(
    ForAll(
        [u, v, w, z],
        And(v != 0, z != 0),
        (u / v) + -1 * (w / z) == (u - w) / v + w * ((z - v) / (v * z)),
    )
)
def div_decomp(l):
    u, v, w, z = l.fixes()
    l.intros()
    l.auto()


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
    Y, X = abs(y), abs(x)
    ea = eps * Y / 4
    eb = min(Y / 2, eps * Y * Y / (4 * (X + 1)))
    l.have(Y > 0, by=[abs_pos_iff(y)])
    l.have(ea > 0, by=[])
    l.have(eb > 0, by=[abs_pos(x), min.defn])
    Pa, Pb = near(a, x, ea), near(b, y, eb)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, ea)])
    l.have(eventually(Pb), by=[eventually_near(b, y, eb)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: split a[m]/b[m] - x/y into a numerator and a denominator error.
    l.have(
        ForAll(
            [n],
            And(abs(a[n] - x) < ea, abs(b[n] - y) < eb),
            abs((a / b)[n] - x / y) < eps,
        )
    )
    l.unfold(div)
    l.beta()
    m = l.fix()
    l.intros()

    am, bm = a[m], b[m]
    da, db, B = abs(am - x), abs(bm - y), abs(bm)
    l.have(And(db < Y / 2, db * (4 * (X + 1)) < eps * Y * Y), by=[min.defn, abs_pos(x)])
    l.have(abs(y - bm) == db, by=[abs_neg(bm - y)])
    l.have(Y <= db + B, by=[abs_triangle(y, RealVal(0), bm)])
    l.have(B > Y / 2, by=[])
    l.have(bm != 0, by=[abs_pos_iff(bm)])
    t1 = (am - x) / bm
    t2 = x * ((y - bm) / (bm * y))
    decomp = l.have(am / bm - x / y == t1 + t2, by=[div_decomp(am, bm, x, y)])
    l.have(abs(t1) == da / B, by=[abs_div(am - x, bm)])
    l.have(
        abs(t2) == X * (db / (B * Y)),
        by=[abs_mul(x, (y - bm) / (bm * y)), abs_div(y - bm, bm * y), abs_mul(bm, y)],
    )
    l.have(da / B < eps / 2, by=[])
    l.have(X * (db / (B * Y)) < eps / 2, by=[abs_pos(x), abs_pos(bm - y)])
    bound = l.have(abs(t1 + t2) < eps, by=[abs_add(t1, t2)])
    # Discharge congruence with just the equality and the scalar bound.
    result = abs(am / bm - x / y) < eps
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

    >>> a, b = Consts("a b", RSeq)
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
