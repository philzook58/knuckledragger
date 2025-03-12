import kdrag.theories.nat as nat
import kdrag as kd
import kdrag.smt as smt
import kdrag.rewrite as rw
def test_add():
    rules = [nat.add_Z, nat.add_S] # [rw.rewrite_of_expr(rule) for rule in [nat.add_Z, nat.add_S]]
    assert kd.rewrite.rewrite(nat.S(nat.Z) + nat.Z, rules).eq(nat.S(nat.Z))

def test_rewrite():
    x, y, z = smt.Reals("x y z")
    succ_0 = smt.ForAll([x], x + 0 == x)
    succ_0_rule = rw.rewrite_of_expr(succ_0)
    vs, lhs, rhs, pf = succ_0_rule
    assert rw.rewrite1(y + 0, vs, lhs, rhs).eq(y)
    t = (y + 0) + 0
    assert rw.rewrite_once(t, [succ_0_rule]).eq(y)
    assert rw.rewrite(t, [succ_0]).eq(y)

    succ_0 = kd.prove(succ_0)
    assert kd.tactics.simp(t, by=[succ_0]).thm.eq(t == y)

    x,y,z = smt.Reals("x y z")
    assert len((((x + x) + x) + x).children()) == 2
    assert rw.rewrite(((x + x) + x) + x, [smt.ForAll([x,y,z], (x + y) + z == x + (y + z))]).arg(0).eq(x)

    