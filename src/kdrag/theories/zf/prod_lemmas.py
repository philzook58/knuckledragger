import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.zf.zf as zf

Set = zf.ZFSet
A, B, p = smt.Consts("A B p", Set)
R = smt.Const("R", Set)
X = smt.Const("X", Set)
Y = smt.Const("Y", Set)
x, y = smt.Consts("x y", Set)


@kd.Theorem(
    smt.ForAll(
        [A, B, p],
        smt.Eq(
            zf.elem(p, zf.prod(A, B)),
            kd.QExists(
                [x, y],
                smt.And(zf.elem(x, A), zf.elem(y, B)),
                p == zf.pair(x, y),
            ),
        ),
    )
)
def elem_prod_strong(l):
    A, B, p = l.fixes()
    l.split()

    # -> direction: use elem_prod and pick fst/snd as witnesses.
    l.intros()
    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.exists(zf.fst(p), zf.snd(p))
    l.split()
    l.auto()
    l.auto()

    # <- direction: use the witnesses to rebuild the fst/snd form.
    l.intros()
    x1, y1 = l.obtain(0)
    l.split(at=0)
    l.rw(zf.elem_prod)
    l.split()
    l.have(p == zf.pair(x1, y1))
    l.auto()
    l.rw(-1)
    l.rw(zf.fst_pair)
    l.auto()
    l.rw(-1)
    l.rw(zf.snd_pair)
    l.auto()
    l.rw(-1)
    l.rw(zf.fst_pair)
    l.rw(zf.snd_pair)
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [A, B, p],
        smt.Eq(
            zf.elem(p, zf.prod(A, B)),
            smt.And(
                zf.elem(zf.fst(p), A),
                smt.And(zf.elem(zf.snd(p), B), p == zf.pair(zf.fst(p), zf.snd(p))),
            ),
        ),
    )
)
def elem_prod_fst_snd_eq(l):
    A, B, p = l.fixes()
    l.rw(zf.elem_prod)
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [R],
        smt.Implies(
            zf.is_rel(R),
            R <= zf.prod(zf.dom(R), zf.ran(R)),
        ),
    )
)
def rel_le_prod(l):
    R = l.fix()
    l.intros()
    l.unfold(zf.le)
    p = l.fix()
    l.intros()

    # Use relation-ness to extract pair witnesses for p.
    l.unfold(zf.is_rel, at=0)
    l.specialize(0, p)
    l.have(zf.is_pair(p), by=[])
    l.unfold(zf.is_pair, at=-1)
    x1, y1 = l.obtain(-1)
    l.have(zf.elem(zf.pair(x1, y1), R))
    l.rw(-1)
    l.auto()

    l.rw(zf.elem_prod)
    l.split()

    # dom(R)
    l.have(p == zf.pair(x1, y1))
    l.auto()
    l.rw(-1)
    l.rw(zf.fst_pair)
    l.unfold(zf.dom)
    l.rw(zf.elem_sep)
    l.beta()
    l.split()
    l.exists(y1)
    l.auto()

    # x1 in bigunion(bigunion(R))
    l.rw(zf.bigunion_ax)
    l.exists(zf.sing(x1))
    l.split()
    l.rw(zf.bigunion_ax)
    l.exists(zf.pair(x1, y1))
    l.split()
    l.auto()
    l.rw(zf.elem_pair)
    l.auto()
    l.rw(zf.elem_sing)
    l.auto()

    # ran(R)
    l.have(p == zf.pair(x1, y1))
    l.auto()
    l.rw(-1)
    l.rw(zf.snd_pair)
    l.unfold(zf.ran)
    l.rw(zf.elem_sep)
    l.beta()
    l.split()
    l.exists(x1)
    l.auto()

    # y1 in bigunion(bigunion(R))
    l.rw(zf.bigunion_ax)
    l.exists(zf.upair(x1, y1))
    l.split()
    l.rw(zf.bigunion_ax)
    l.exists(zf.pair(x1, y1))
    l.split()
    l.auto()
    l.rw(zf.elem_pair)
    l.auto()
    l.rw(zf.elem_upair)
    l.auto()

    l.have(p == zf.pair(x1, y1))
    l.auto()
    l.rw(-1)
    l.rw(zf.fst_pair)
    l.rw(zf.snd_pair)
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [A, B, X],
        zf.prod(A | B, X) == zf.prod(A, X) | zf.prod(B, X),
    )
)
def prod_union_left(l):
    A, B, X = l.fixes()
    l.rw(zf.ext_ax)
    _p = l.fix()
    l.rw(zf.elem_union)
    l.split()

    # -> : element of prod(A | B, X) is in prod(A, X) or prod(B, X)
    l.intros()
    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_union, at=0)
    l.split(at=0)
    l.right()
    l.rw(zf.elem_prod)
    l.auto()

    l.left()
    l.rw(zf.elem_prod)
    l.auto()

    # <- : element of prod(A, X) or prod(B, X) is in prod(A | B, X)
    l.intros()
    l.split(at=0)

    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_prod)
    l.split()
    l.rw(zf.elem_union)
    l.auto()
    l.auto()
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [A, B, X, Y, p],
        smt.Implies(
            zf.elem(p, zf.prod(A & B, X & Y)),
            zf.elem(p, zf.prod(A, X) & zf.prod(B, Y)),
        ),
    )
)
def prod_inter_le(l):
    A, B, X, Y, p = l.fixes()
    l.intros()
    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_inter, at=0)
    l.split(at=0)
    l.rw(zf.elem_inter, at=2)
    l.split(at=2)
    l.rw(zf.elem_inter)
    l.split()
    l.rw(zf.elem_prod)
    l.auto()
    l.rw(zf.elem_prod)
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [A, B, X, Y, p],
        smt.Implies(
            zf.elem(p, zf.prod(A, X) & zf.prod(B, Y)),
            zf.elem(p, zf.prod(A & B, X & Y)),
        ),
    )
)
def prod_inter_ge(l):
    A, B, X, Y, p = l.fixes()
    l.intros()
    l.rw(zf.elem_inter, at=0)
    l.split(at=0)

    l.rw(zf.elem_prod, at=0)
    l.split(at=0)

    l.rw(zf.elem_prod, at=3)
    l.split(at=3)

    l.rw(zf.elem_prod)
    l.split()
    l.rw(zf.elem_inter)
    l.auto()
    l.rw(zf.elem_inter)
    l.auto()
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [A, B, X, Y],
        zf.prod(A & B, X & Y) == zf.prod(A, X) & zf.prod(B, Y),
    )
)
def prod_inter_dist(l):
    A, B, X, Y = l.fixes()
    l.rw(zf.ext_ax)
    _p = l.fix()
    l.split()

    # left -> right
    l.intros()
    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_inter, at=0)
    l.split(at=0)
    l.rw(zf.elem_inter, at=2)
    l.split(at=2)
    l.rw(zf.elem_inter)
    l.split()
    l.rw(zf.elem_prod)
    l.auto()
    l.rw(zf.elem_prod)
    l.auto()

    # right -> left
    l.intros()
    l.rw(zf.elem_inter, at=0)
    l.split(at=0)

    l.rw(zf.elem_prod, at=0)
    l.split(at=0)

    l.rw(zf.elem_prod, at=3)
    l.split(at=3)

    l.rw(zf.elem_prod)
    l.split()
    l.rw(zf.elem_inter)
    l.auto()
    l.rw(zf.elem_inter)
    l.auto()
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [A, B, X],
        zf.prod(X, A | B) == zf.prod(X, A) | zf.prod(X, B),
    )
)
def prod_union_right(l):
    A, B, X = l.fixes()
    l.rw(zf.ext_ax)
    _p = l.fix()
    l.rw(zf.elem_union)
    l.split()

    # -> : element of prod(X, A | B) is in prod(X, A) or prod(X, B)
    l.intros()
    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_union, at=1)
    l.split(at=1)
    l.right()
    l.rw(zf.elem_prod)
    l.auto()

    l.left()
    l.rw(zf.elem_prod)
    l.auto()

    # <- : element of prod(X, A) or prod(X, B) is in prod(X, A | B)
    l.intros()
    l.split(at=0)

    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_prod)
    l.split()
    l.auto()
    l.rw(zf.elem_union)
    l.auto()
    l.auto()

    l.rw(zf.elem_prod, at=0)
    l.split(at=0)
    l.rw(zf.elem_prod)
    l.split()
    l.auto()
    l.rw(zf.elem_union)
    l.auto()
    l.auto()
