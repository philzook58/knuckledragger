"""Prototype of strict user names and prefixed datatype declarations."""

import pytest
import kdrag as kd
import kdrag.smt as smt
from kdrag.printers.tptp import expr_to_tptp
from kdrag.solvers import BaseSolver, EProverSolver


def export(tmp_path, *formulas):
    s = BaseSolver()
    for formula in formulas:
        s.add(formula)
    p = tmp_path / "problem.p"
    s.write_tptp(p, format="tff")
    return p.read_text()


@pytest.mark.parametrize("name", ["vec3.add", "BadName", "space name", "kd_user"])
def test_invalid_name(tmp_path, name):
    with pytest.raises(ValueError, match="Non-portable"):
        export(tmp_path, smt.Bool(name))


def test_overloading_rejected(tmp_path):
    with pytest.raises(ValueError, match="overloading"):
        export(tmp_path, smt.Int("same") == 1, smt.Real("same") == 2)


def test_sort_collision_rejected(tmp_path):
    a = smt.Const("a", smt.DeclareSort("Collision"))
    b = smt.Const("b", smt.DeclareSort("collision"))
    with pytest.raises(ValueError, match="sort-name collision"):
        export(tmp_path, a == a, b == b)


def test_sort_function_collision(tmp_path):
    a = smt.Const("shared_name", smt.DeclareSort("shared_name"))
    with pytest.raises(ValueError, match="sort/function name collision"):
        export(tmp_path, a == a)


def test_unchanged_names_and_fresh_names(tmp_path):
    x, y = smt.Ints("x y")
    f = smt.Function("vec3_add", smt.IntSort(), smt.IntSort())
    text = export(tmp_path, f(x) == x, smt.FreshBool())
    assert "vec3_add :" in text
    assert "vec3_add(x)" in text
    assert "kd_f_" in text
    assert "![V0:$int, V1:$int]" in expr_to_tptp(
        smt.ForAll([x, y], smt.Exists([smt.Int("z")], x == y))
    )
    assert "V2:$int" in expr_to_tptp(
        smt.ForAll([x, y], smt.Exists([smt.Int("z")], x == y))
    )


def test_portable_datatype_python_api(tmp_path):
    P = kd.Struct(
        "PortableNamesPoint", ("x", smt.IntSort()), ("y", smt.IntSort()), portable=True
    )
    Q = kd.Struct("PortableNamesOther", ("x", smt.IntSort()), portable=True)
    assert P.accessor(0, 0).name() == "portablenamespoint_x"
    p = P(x=1, y=2)
    kd.prove(p.x == 1)
    kd.prove(p._replace(y=3).y == 3)
    kd.prove(p.is_PortableNamesPoint)
    text = export(tmp_path, p.x == Q(1).x)
    assert "portablenamespoint_x" in text
    assert "portablenamesother_x" in text


def test_portable_inductive():
    N = kd.Inductive("PortableNamesNat", portable=True)
    N.declare("zero")
    N.declare("succ", ("pred", N))
    N = N.create()
    kd.prove(N.succ(N.zero).pred == N.zero)
    kd.prove(N.zero.is_zero)
    assert kd.datatype.constructor_num(N, "succ") == 1


def test_duplicate_public_fields():
    N = kd.Inductive("PortableNamesDuplicate", portable=True)
    N.declare("a", ("x", smt.IntSort()))
    N.declare("b", ("x", smt.IntSort()))
    with pytest.raises(ValueError, match="Duplicate public"):
        N.create()


def test_eprover_portable_record():
    pytest.importorskip("eprover")
    T = smt.DeclareSort("PortableScalar")
    P = kd.Struct("PortableNamesPair", ("x", T), ("y", T), portable=True)
    p, q = smt.Consts("p q", P)
    swap = kd.define("portable_pair_swap", [p], P(p.y, p.x))
    kd.prove(
        smt.ForAll([p, q], p == q, swap(p) == swap(q)),
        by=[swap.defn],
        solver=EProverSolver,
    )
