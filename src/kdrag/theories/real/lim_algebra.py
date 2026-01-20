import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real
import kdrag.theories.real.seq as seq

RSeq = real.RSeq


a, b = smt.Consts("a b", RSeq)
x, y, c = smt.Reals("x y c")
u, v, w, z = smt.Reals("u v w z")

n = smt.Int("n")


@kd.Theorem(
    smt.ForAll(
        [a, x, c],
        seq.has_lim(a, x),
        seq.has_lim(seq.smul(c, a), c * x),
    ),
)
def has_lim_smul(l):
    a, x, c = l.fixes()
    l.intros()
    l.cases(c == 0)

    # Zero scalar: smul is constant zero, so limit is zero.
    l.have(c == 0, by=[])
    l.unfold(seq.has_lim)
    eps = l.fix()
    l.assumes(eps > 0)
    l.exists(smt.IntVal(0))
    n = l.fix()
    l.assumes(n > 0)
    l.unfold(seq.smul)
    l.simp()
    l.unfold(real.abs)
    l.simp()
    l.auto()

    # Nonzero scalar: pull out |c| and use the original limit with eps/|c|.
    l.unfold(seq.has_lim, at=0)
    hlim = l.top_goal().ctx[0]
    l.have(c != 0, by=[])
    l.unfold(seq.has_lim)
    eps = l.fix()
    l.assumes(eps > 0)
    eps1 = eps / real.abs(c)
    l.have(real.abs(c) > 0, by=[real.abs_pos_iff])
    l.have(eps1 > 0, by=[])
    l.specialize(hlim, eps1)
    N = smt.Int("N")
    n_var = smt.Int("n")
    exists_n = kd.QExists(
        [N],
        kd.QForAll([n_var], n_var > N, real.abs(a[n_var] - x) < eps1),
    )
    l.have(exists_n, by=[])
    N1 = l.obtain(exists_n)
    l.exists(N1)
    n = l.fix()
    l.assumes(n > N1)
    forall_n = kd.QForAll([n_var], n_var > N1, real.abs(a[n_var] - x) < eps1)
    l.specialize(forall_n, n)
    l.have(real.abs(a[n] - x) < eps1, by=[])
    l.unfold(seq.smul)
    l.simp()
    # Reassociate to factor c, then rewrite using abs_mul.
    l.have(c * a[n] + -1 * c * x == c * (a[n] - x), by=[])
    l.have(
        real.abs(c * (a[n] - x)) == real.abs(c) * real.abs(a[n] - x),
        by=[real.abs_mul],
    )
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [a, b, x, y],
        seq.has_lim(a, x),
        seq.has_lim(b, y),
        seq.has_lim(a + b, x + y),
    )
)
def has_lim_add(l):
    a, b, x, y = l.fixes()
    l.intros()
    l.split(at=0)
    l.unfold(seq.has_lim)
    eps = l.fix()
    l.assumes(eps > 0)
    eps2 = eps / 2
    l.have(eps2 > 0, by=[])

    # Use the two limits with eps/2.
    l.unfold(seq.has_lim, at=0)
    l.unfold(seq.has_lim, at=1)
    l.specialize(0, eps2)
    l.specialize(1, eps2)
    N1 = smt.Int("N")
    N2 = smt.Int("N")
    n_var = smt.Int("n")
    exists_a = kd.QExists(
        [N1],
        kd.QForAll([n_var], n_var > N1, real.abs(a[n_var] - x) < eps2),
    )
    exists_b = kd.QExists(
        [N2],
        kd.QForAll([n_var], n_var > N2, real.abs(b[n_var] - y) < eps2),
    )
    l.have(exists_a, by=[])
    N1v = l.obtain(exists_a)
    l.have(exists_b, by=[])
    N2v = l.obtain(exists_b)

    # Choose a common bound for both tails.
    N = smt.If(N1v > N2v, N1v, N2v) + 1
    l.exists(N)
    n = l.fix()
    l.assumes(n > N)
    l.have(n > N1v, by=[])
    l.have(n > N2v, by=[])

    forall_a = kd.QForAll([n_var], n_var > N1v, real.abs(a[n_var] - x) < eps2)
    forall_b = kd.QForAll([n_var], n_var > N2v, real.abs(b[n_var] - y) < eps2)
    l.specialize(forall_a, n)
    l.specialize(forall_b, n)
    l.have(real.abs(a[n] - x) < eps2, by=[])
    l.have(real.abs(b[n] - y) < eps2, by=[])

    # Expand the sum and use abs_add to bound by eps/2 + eps/2.
    l.unfold(seq.add)
    l.simp()
    l.have((a[n] + b[n]) - (x + y) == (a[n] - x) + (b[n] - y), by=[])
    l.have(
        real.abs((a[n] - x) + (b[n] - y)) <= real.abs(a[n] - x) + real.abs(b[n] - y),
        by=[real.abs_add],
    )
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [a, b, x, y],
        seq.has_lim(a, x),
        seq.has_lim(b, y),
        seq.has_lim(a * b, x * y),
    )
)
def has_lim_mul(l):
    a, b, x, y = l.fixes()
    l.intros()
    l.split(at=0)
    l.unfold(seq.has_lim)
    eps = l.fix()
    l.assumes(eps > 0)

    # Set eps/2 bounds and also get a tail where |b - y| < 1.
    eps1 = eps / (2 * (real.abs(y) + 1))
    eps2 = eps / (2 * (real.abs(x) + 1))
    l.have(real.abs(y) + 1 > 0, by=[real.abs_pos])
    l.have(real.abs(x) + 1 > 0, by=[real.abs_pos])
    l.have(eps1 > 0, by=[])
    l.have(eps2 > 0, by=[])

    l.unfold(seq.has_lim, at=0)
    l.unfold(seq.has_lim, at=1)
    l.specialize(0, eps1)
    l.specialize(1, eps2)

    l.have(smt.RealVal(1) > 0, by=[])
    l.specialize(1, smt.RealVal(1))

    N1 = smt.Int("N")
    N2 = smt.Int("N")
    N3 = smt.Int("N")
    n_var = smt.Int("n")
    exists_a = kd.QExists(
        [N1],
        kd.QForAll([n_var], n_var > N1, real.abs(a[n_var] - x) < eps1),
    )
    exists_b = kd.QExists(
        [N2],
        kd.QForAll([n_var], n_var > N2, real.abs(b[n_var] - y) < eps2),
    )
    exists_b1 = kd.QExists(
        [N3],
        kd.QForAll([n_var], n_var > N3, real.abs(b[n_var] - y) < 1),
    )
    l.have(exists_a, by=[])
    N1v = l.obtain(exists_a)
    l.have(exists_b, by=[])
    N2v = l.obtain(exists_b)
    l.have(exists_b1, by=[])
    N3v = l.obtain(exists_b1)

    # Use a common tail for all three estimates.
    N = smt.If(N1v > N2v, N1v, N2v)
    N = smt.If(N > N3v, N, N3v) + 1
    l.exists(N)
    n = l.fix()
    l.assumes(n > N)
    l.have(n > N1v, by=[])
    l.have(n > N2v, by=[])
    l.have(n > N3v, by=[])

    forall_a = kd.QForAll([n_var], n_var > N1v, real.abs(a[n_var] - x) < eps1)
    forall_b = kd.QForAll([n_var], n_var > N2v, real.abs(b[n_var] - y) < eps2)
    forall_b1 = kd.QForAll([n_var], n_var > N3v, real.abs(b[n_var] - y) < 1)
    l.specialize(forall_a, n)
    l.specialize(forall_b, n)
    l.specialize(forall_b1, n)
    l.have(real.abs(a[n] - x) < eps1, by=[])
    l.have(real.abs(b[n] - y) < eps2, by=[])
    l.have(real.abs(b[n] - y) < 1, by=[])
    l.have(real.abs(a[n] - x) >= 0, by=[real.abs_pos])
    l.have(real.abs(b[n] - y) >= 0, by=[real.abs_pos])
    l.have(real.abs(b[n]) >= 0, by=[real.abs_pos])
    l.have(real.abs(x) >= 0, by=[real.abs_pos])
    l.have(real.abs(y) >= 0, by=[real.abs_pos])

    # Control |b[n]| using the triangle inequality.
    l.have(
        real.abs(b[n]) <= real.abs(b[n] - y) + real.abs(y),
        by=[real.abs_triangle(b[n], smt.RealVal(0), y)],
    )
    l.have(real.abs(b[n]) < real.abs(y) + 1, by=[])
    l.have(real.abs(b[n]) <= real.abs(y) + 1, by=[])
    l.have(real.abs(x) <= real.abs(x) + 1, by=[])
    l.have(
        eps1 * (real.abs(y) + 1) == eps / 2,
        by=[],
    )
    l.have(
        eps2 * (real.abs(x) + 1) == eps / 2,
        by=[],
    )

    # Expand and bound |a*b - x*y|.
    l.unfold(seq.mul)
    l.simp()
    l.have(a[n] * b[n] + -1 * (x * y) == (a[n] - x) * b[n] + x * (b[n] - y), by=[])
    l.have(
        real.abs((a[n] - x) * b[n] + x * (b[n] - y))
        <= real.abs((a[n] - x) * b[n]) + real.abs(x * (b[n] - y)),
        by=[real.abs_add],
    )
    l.have(
        real.abs((a[n] - x) * b[n]) == real.abs(a[n] - x) * real.abs(b[n]),
        by=[real.abs_mul],
    )
    l.have(
        real.abs(x * (b[n] - y)) == real.abs(x) * real.abs(b[n] - y),
        by=[real.abs_mul],
    )
    l.have(
        real.abs(a[n] - x) * real.abs(b[n]) < eps / 2,
        by=[],
    )
    l.have(
        real.abs(x) * real.abs(b[n] - y) < eps / 2,
        by=[],
    )
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [u, v, w, z],
        smt.Implies(
            smt.And(v != 0, z != 0),
            (u / v) + -1 * (w / z) == (u - w) / v + w * ((z - v) / (v * z)),
        ),
    )
)
def div_decomp(l):
    u, v, w, z = l.fixes()
    l.intros()
    l.auto()


"""
# unstable
@kd.Theorem(
    smt.ForAll(
        [a, b, x, y],
        smt.Implies(
            smt.And(
                seq.has_lim(a, x),
                seq.has_lim(b, y),
                kd.QForAll([n], b[n] != 0),
                y != 0,
            ),
            seq.has_lim(a / b, x / y),
        ),
    )
)

def has_lim_div(l):
    a, b, x, y = l.fixes()
    l.intros()
    l.split(at=0)
    l.unfold(seq.has_lim)
    eps = l.fix()
    l.assumes(eps > 0)

    # Choose eps-splitting constants and a lower bound on |y|.
    abs_y = real.abs(y)
    l.have(abs_y > 0, by=[real.abs_pos_iff])
    l.have(abs_y / 2 > 0, by=[])
    l.have(real.abs(x) + 1 > 0, by=[real.abs_pos])

    # We'll need small tails for a and b, plus a tail keeping b away from 0.
    eps_a = eps * abs_y / 4
    eps_b = eps * abs_y * abs_y / (4 * (real.abs(x) + 1))
    l.have(eps_a > 0, by=[])
    l.have(eps_b > 0, by=[])

    # Pull limits for a and b at the needed eps.
    l.unfold(seq.has_lim, at=0)
    l.unfold(seq.has_lim, at=1)
    l.specialize(0, eps_a)
    l.specialize(1, eps_b)
    l.specialize(1, abs_y / 2)

    N1 = smt.Int("N")
    N2 = smt.Int("N")
    N3 = smt.Int("N")
    n_var = smt.Int("n")
    exists_a = kd.QExists(
        [N1],
        kd.QForAll([n_var], n_var > N1, real.abs(a[n_var] - x) < eps_a),
    )
    exists_b = kd.QExists(
        [N2],
        kd.QForAll([n_var], n_var > N2, real.abs(b[n_var] - y) < eps_b),
    )
    exists_b2 = kd.QExists(
        [N3],
        kd.QForAll([n_var], n_var > N3, real.abs(b[n_var] - y) < abs_y / 2),
    )
    l.have(exists_a, by=[])
    N1v = l.obtain(exists_a)
    l.have(exists_b, by=[])
    N2v = l.obtain(exists_b)
    l.have(exists_b2, by=[])
    N3v = l.obtain(exists_b2)

    N = smt.If(N1v > N2v, N1v, N2v)
    N = smt.If(N > N3v, N, N3v) + 1
    l.exists(N)
    n = l.fix()
    l.assumes(n > N)
    l.have(n > N1v, by=[])
    l.have(n > N2v, by=[])
    l.have(n > N3v, by=[])

    forall_a = kd.QForAll([n_var], n_var > N1v, real.abs(a[n_var] - x) < eps_a)
    forall_b = kd.QForAll([n_var], n_var > N2v, real.abs(b[n_var] - y) < eps_b)
    forall_b2 = kd.QForAll([n_var], n_var > N3v, real.abs(b[n_var] - y) < abs_y / 2)
    l.specialize(forall_a, n)
    l.specialize(forall_b, n)
    l.specialize(forall_b2, n)
    l.have(real.abs(a[n] - x) < eps_a, by=[])
    l.have(real.abs(b[n] - y) < eps_b, by=[])
    l.have(real.abs(b[n] - y) < abs_y / 2, by=[])
    # Nonneg facts for arithmetic bounds.
    l.have(real.abs(a[n] - x) >= 0, by=[real.abs_pos])
    l.have(real.abs(b[n] - y) >= 0, by=[real.abs_pos])
    l.have(real.abs(b[n]) >= 0, by=[real.abs_pos])
    l.have(real.abs(x) >= 0, by=[real.abs_pos])

    # Lower bound |b[n]| from |b[n] - y| < |y|/2, then use b[n] != 0.
    l.have(real.abs(y - b[n]) == real.abs(b[n] - y), by=[real.abs_neg])
    l.have(
        abs_y <= real.abs(b[n] - y) + real.abs(b[n]), by=[real.abs_triangle(y, 0, b[n])]
    )
    l.have(real.abs(b[n]) > abs_y / 2, by=[])
    l.have(real.abs(b[n]) >= abs_y / 2, by=[])
    bn_nonzero = kd.QForAll([n_var], b[n_var] != 0)
    l.have(bn_nonzero, by=[])
    l.specialize(bn_nonzero, n)
    l.have(b[n] != 0, by=[])
    l.have(b[n] * y != 0, by=[])

    # Expand and bound |a/b - x/y| by two terms, then apply abs_div.
    l.unfold(seq.div)
    l.simp()
    t1 = (a[n] - x) / b[n]
    t2 = x * ((y - b[n]) / (b[n] * y))
    l.have(
        a[n] / b[n] + -1 * (x / y) == t1 + t2,
        by=[div_decomp(a[n], b[n], x, y)],
    )
    l.have(
        real.abs(t1 + t2) <= real.abs(t1) + real.abs(t2),
        by=[real.abs_add(t1, t2)],
    )
    l.have(
        real.abs(t1) == real.abs(a[n] - x) / real.abs(b[n]),
        by=[real.abs_div(a[n] - x, b[n])],
    )
    l.have(
        real.abs(t2) == real.abs(x) * (real.abs(y - b[n]) / real.abs(b[n] * y)),
        by=[real.abs_mul(x, (y - b[n]) / (b[n] * y)), real.abs_div(y - b[n], b[n] * y)],
    )
    l.have(
        real.abs(b[n] * y) == real.abs(b[n]) * abs_y,
        by=[real.abs_mul(b[n], y)],
    )
    l.have(
        real.abs(a[n] - x) / real.abs(b[n]) < eps / 2,
        by=[],
    )
    l.have(
        real.abs(x) * (real.abs(y - b[n]) / real.abs(b[n] * y)) < eps / 2,
        by=[],
    )
    l.auto()
"""
