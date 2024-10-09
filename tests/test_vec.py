import kdrag.theories.vec as vec
import kdrag.smt as smt
import kdrag as kd


def test_enum():
    assert len(vec.ind3) == 3


def test_vec():
    Vec3 = vec.Vec(3)
    u, v, w = smt.Consts("u v w", Vec3)
    assert u.x0.eq(u.x0)
    kd.lemma(u + v == v + u, by=[kd.notation.add[Vec3].defn])
    vec.VecTheory(Vec3)
