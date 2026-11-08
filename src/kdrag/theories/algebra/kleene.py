"""
Kleene Algebra


- https://www.philipzucker.com/bryzzowski_kat/
- https://www.cs.uoregon.edu/research/summerschool/summer24/topics.php#Silva

"""

import kdrag as kd
from kdrag import Theorem, axiom, prove
from kdrag.smt import Const, Consts, DeclareSort, Eq, ForAll, Function

K = DeclareSort("Kleene")
zero = Const("_0", K)
one = Const("_1", K)
x, y, z, w, e, f = Consts("x y z w e f", K)
par = Function("Kleene.par", K, K, K)
seq = Function("Kleene.seq", K, K, K)
star = Function("Kleene.star", K, K)
kd.notation.or_.register(K, par)
kd.notation.add.register(K, par)
kd.notation.matmul.register(K, seq)
kd.notation.mul.register(K, seq)
kd.notation.le.register(K, lambda x, y: Eq(par(x, y), y))


par_assoc = axiom(ForAll([x, y, z], x + (y + z) == (x + y) + z))
par_comm = axiom(ForAll([x, y], x + y == y + x))
par_idem = axiom(ForAll([x], x + x == x))
par_zero = axiom(ForAll([x], x + zero == x))

zero_par = prove(ForAll([x], zero + x == x), by=[par_comm, par_zero])

seq_assoc = axiom(ForAll([x, y, z], x * (y * z) == (x * y) * z))
seq_zero = axiom(ForAll([x], x * zero == zero))
seq_one = axiom(ForAll([x], x * one == x))

rdistrib = axiom(ForAll([x, y, z], x * (y + z) == x * y + x * z))
ldistrib = axiom(ForAll([x, y, z], (y + z) * x == y * x + z * x))

unfold = axiom(ForAll([e], star(e) == one + e * star(e)))

# If a set shrinks, star(e) is less than it

least_fix = axiom(ForAll([x, e, f], f + e * x <= x, star(e) * f <= x))

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

par_monotone = prove(
    ForAll([x, y, z, w], x <= y, z <= w, x + z <= y + w),
    by=[par_assoc, par_comm],
)

seq_monotone = prove(
    ForAll([x, y, z, w], x <= y, z <= w, x * z <= y * w),
    by=[rdistrib, ldistrib, par_assoc],
)


@Theorem(ForAll([x], x <= star(x)))
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


@Theorem(ForAll([x], star(x) * star(x) == star(x)))
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


@Theorem(ForAll([x], star(star(x)) == star(x)))
def star_star(l):
    x = l.fix()
    sx = star(x)
    l.have(one <= sx, by=[unfold(x), par_assoc, par_comm, par_idem])
    # The product lemma makes sx a pre-fixpoint for another star.
    l.have(one + sx * sx <= sx, by=[star_seq_star(x), par_idem(sx)])
    l.have(star(sx) <= sx, by=[least_fix(sx, sx, one), seq_one(star(sx))])
    l.auto(by=[star_incl(sx), par_comm(star(sx), sx)])


Test = DeclareSort("Test")
guard = Function("Test.guard", Test, K, K)
and_ = Function("Test.and", Test, Test, Test)
or_ = Function("Test.or", Test, Test, Test)
not_ = Function("Test.not", Test, Test)
true = Const("Test.true", Test)
false = Const("Test.false", Test)
kd.notation.invert.register(Test, not_)

a, b, c, d = Consts("a b c d", Test)


def while_(t, c):
    return star(guard(t, c)) * guard(~t, one)
