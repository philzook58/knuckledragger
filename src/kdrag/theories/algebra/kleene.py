"""
Kleene Algebra


- https://www.philipzucker.com/bryzzowski_kat/
- https://www.cs.uoregon.edu/research/summerschool/summer24/topics.php#Silva

"""

import kdrag as kd
import kdrag.smt as smt

K = smt.DeclareSort("Kleene")
zero = smt.Const("_0", K)
one = smt.Const("_1", K)
x, y, z, w, e, f = smt.Consts("x y z w e f", K)
par = smt.Function("Kleene.par", K, K, K)
seq = smt.Function("Kleene.seq", K, K, K)
star = smt.Function("Kleene.star", K, K)
kd.notation.or_.register(K, par)
kd.notation.add.register(K, par)
kd.notation.matmul.register(K, seq)
kd.notation.mul.register(K, seq)
kd.notation.le.register(K, lambda x, y: smt.Eq(par(x, y), y))


par_assoc = kd.axiom(smt.ForAll([x, y, z], x + (y + z) == (x + y) + z))
par_comm = kd.axiom(smt.ForAll([x, y], x + y == y + x))
par_idem = kd.axiom(smt.ForAll([x], x + x == x))
par_zero = kd.axiom(smt.ForAll([x], x + zero == x))

zero_par = kd.prove(smt.ForAll([x], zero + x == x), by=[par_comm, par_zero])

seq_assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
seq_zero = kd.axiom(smt.ForAll([x], x * zero == zero))
seq_one = kd.axiom(smt.ForAll([x], x * one == x))

rdistrib = kd.axiom(smt.ForAll([x, y, z], x * (y + z) == x * y + x * z))
ldistrib = kd.axiom(smt.ForAll([x, y, z], (y + z) * x == y * x + z * x))

unfold = kd.axiom(smt.ForAll([e], star(e) == one + e * star(e)))

# If a set shrinks, star(e) is less than it

least_fix = kd.axiom(smt.ForAll([x, e, f], f + e * x <= x, star(e) * f <= x))

KLEENE = [
    par_assoc,
    par_comm,
    par_idem,
    par_zero,
    seq_assoc,
    seq_zero,
    seq_one,
    rdistrib,
    ldistrib,
    unfold,
    least_fix,
]

par_monotone = kd.prove(
    smt.ForAll([x, y, z, w], x <= y, z <= w, x + z <= y + w),
    by=[par_assoc, par_comm],
)

seq_monotone = kd.prove(
    smt.ForAll([x, y, z, w], x <= y, z <= w, x * z <= y * w),
    by=[rdistrib, ldistrib, par_assoc],
)

@kd.Theorem(smt.ForAll([x], x <= star(x)))
def star_incl(l):
    x = l.fix()
    sx = star(x)
    l.have(one <= sx, by=[unfold(x), par_assoc, par_comm, par_idem])
    l.have(x * sx <= sx, by=[unfold(x), par_assoc, par_comm, par_idem])
    l.auto(
        by=[
            seq_monotone(x, x, one, sx),
            seq_one(x),
            par_idem(x),
            par_assoc(x, x * sx, sx),
        ]
    )


@kd.Theorem(smt.ForAll([x], star(x) * star(x) == star(x)))
def star_seq_star(l):
    x = l.fix()
    sx = star(x)
    l.have(one <= sx, by=[unfold(x), par_assoc, par_comm, par_idem])
    # Induction bounds the product above; monotonicity bounds it below.
    l.have(sx + x * sx <= sx, by=[unfold(x), par_assoc, par_comm, par_idem])
    l.have(sx * sx <= sx, by=[least_fix(sx, x, sx)])
    l.have(
        sx <= sx * sx,
        by=[seq_monotone(sx, sx, one, sx), seq_one(sx), par_idem(sx)],
    )
    l.auto(by=[par_comm(sx * sx, sx)])


@kd.Theorem(smt.ForAll([x], star(star(x)) == star(x)))
def star_star(l):
    x = l.fix()
    sx = star(x)
    l.have(one <= sx, by=[unfold(x), par_assoc, par_comm, par_idem])
    # The product lemma makes sx a pre-fixpoint for another star.
    l.have(one + sx * sx <= sx, by=[star_seq_star(x), par_idem(sx)])
    l.have(star(sx) <= sx, by=[least_fix(sx, sx, one), seq_one(star(sx))])
    l.auto(by=[star_incl(sx), par_comm(star(sx), sx)])


Test = smt.DeclareSort("Test")
guard = smt.Function("Test.guard", Test, K, K)
and_ = smt.Function("Test.and", Test, Test, Test)
or_ = smt.Function("Test.or", Test, Test, Test)
not_ = smt.Function("Test.not", Test, Test)
true = smt.Const("Test.true", Test)
false = smt.Const("Test.false", Test)
kd.notation.invert.register(Test, not_)

a, b, c, d = smt.Consts("a b c d", Test)


def while_(t, c):
    return star(guard(t, c)) * guard(~t, one)
