import shutil

import pytest

import kdrag as kd
import kdrag.config as config
import kdrag.proof_cache as proof_cache
import kdrag.smt as smt


@pytest.fixture
def cache(tmp_path, monkeypatch):
    monkeypatch.setattr(config, "cache", True)
    monkeypatch.setattr(config, "cache_dir", str(tmp_path / "cache"))
    monkeypatch.setattr(proof_cache, "_dir", None)
    monkeypatch.setattr(proof_cache, "hits", 0)
    monkeypatch.setattr(proof_cache, "misses", 0)
    return tmp_path / "cache"


def no_solving(monkeypatch):
    def check(self, *args):
        raise AssertionError("solver called on a cache hit")

    monkeypatch.setattr(smt.Z3Solver, "check", check)


def key(by, thm):
    return proof_cache.key(smt.Implies(smt.And(by), thm))


def test_cache_miss_then_hit(cache, monkeypatch):
    x = smt.Int("x")
    kd.prove(x + 1 > x)
    assert (proof_cache.hits, proof_cache.misses) == (0, 1)
    assert (cache / "proofs.txt").exists() and (cache / "secret").exists()
    no_solving(monkeypatch)
    kd.prove(x + 1 > x)
    assert proof_cache.hits == 1


def test_cache_reload_from_disk(cache, monkeypatch):
    x = smt.Int("x")
    kd.prove(x * x >= 0)
    monkeypatch.setattr(proof_cache, "_dir", None)
    monkeypatch.setattr(proof_cache, "_digests", set())
    no_solving(monkeypatch)
    kd.prove(x * x >= 0)
    assert proof_cache.hits == 1


def test_cache_fresh_names_shared_between_by_and_goal(cache):
    x5 = smt.FreshConst(smt.IntSort(), prefix="x")
    x7 = smt.FreshConst(smt.IntSort(), prefix="x")
    hyp = kd.axiom(x5 > 0)
    kd.prove(x5 > -1, by=[hyp])
    assert key([x5 > 0], x5 > -1) != key([x5 > 0], x7 > -1)
    with pytest.raises(kd.kernel.SolverFailure):
        kd.prove(x7 > -1, by=[hyp])


def test_cache_fresh_names_renumbered(cache, monkeypatch):
    x1 = smt.FreshConst(smt.IntSort(), prefix="x")
    kd.prove(x1 * x1 >= 0)
    _junk = [smt.FreshConst(smt.IntSort(), prefix="x") for _ in range(5)]
    x2 = smt.FreshConst(smt.IntSort(), prefix="x")
    no_solving(monkeypatch)
    kd.prove(x2 * x2 >= 0)
    assert proof_cache.hits == 1


def test_cache_strings_not_renamed(cache):
    s = smt.String("s")
    assert key([], smt.StringVal("a!1") == s) != key([], smt.StringVal("a!2") == s)


def test_cache_refuses_ambiguous_text(cache):
    xi, xr = smt.Int("x"), smt.Real("x")
    assert key([xr > 0], xi == xi) is None
    L1 = smt.Datatype("CacheL1")
    L1.declare("nil")
    L1 = L1.create()
    L2 = smt.Datatype("CacheL2")
    L2.declare("nil")
    L2 = L2.create()
    assert key([], smt.And(L1.nil == L1.nil, L2.nil == L2.nil)) is None
    abs_ = smt.Function("abs", smt.RealSort(), smt.RealSort())
    assert key([abs_(xr) >= 0], smt.Abs(xr) >= 0) is None
    seq_len = smt.Function("seq.len", smt.IntSort(), smt.IntSort())
    assert key([], seq_len(1) == seq_len(1)) is None
    let_name = smt.Int("?x3")
    assert key([], let_name == let_name) is None


def test_cache_refuses_captured_variables(cache):
    # Instantiating `ForAll y, ForAll x, R(x, y)` with the constant `x` prints like `ForAll x, R(x, x)`.
    x, y, z = smt.Ints("x y z")
    R = smt.Function("R", smt.IntSort(), smt.IntSort(), smt.BoolSort())
    S = smt.Function("S", smt.IntSort(), smt.BoolSort())
    refl = kd.axiom(smt.ForAll([z], R(z, z)))
    sx = kd.axiom(S(x))
    kd.kernel.prove(smt.ForAll([x], R(x, x)), by=[refl, sx])
    captured = kd.axiom(smt.ForAll([y], smt.ForAll([x], R(x, y))))(x).thm
    assert key([refl.thm, sx.thm], captured) is None
    with pytest.raises(kd.kernel.SolverFailure):
        kd.kernel.prove(captured, by=[refl, sx])


def test_cache_other_secret_misses(cache, tmp_path, monkeypatch):
    x = smt.Int("x")
    kd.prove(x + 2 > x)
    other = tmp_path / "other"
    other.mkdir()
    shutil.copy(cache / "proofs.txt", other / "proofs.txt")
    with open(other / "proofs.txt", "a") as f:
        f.write("not a digest\n" + "0" * 63 + "\n")
    monkeypatch.setattr(config, "cache_dir", str(other))
    kd.prove(x + 2 > x)
    assert proof_cache.hits == 0


def test_cache_bypassed(cache):
    x = smt.Int("x")
    kd.prove(x + 3 > x, solver=lambda: smt.Z3Solver())
    kd.prove(x + 3 > x, admit=True)
    assert not cache.exists()
    config.cache = False
    kd.prove(x + 3 > x)
    assert not cache.exists()


def test_cache_key_ignores_print_settings(cache):
    # The printer's lets depend on reference counts, so reuse one formula.
    x = smt.Int("x")
    fml = smt.Implies(x > 0, x * x > 0)
    k = proof_cache.key(fml)
    old = smt.get_param("pp.max_depth")
    smt.set_param("pp.max_depth", 2)
    try:
        assert proof_cache.key(fml) == k
    finally:
        smt.set_param("pp.max_depth", old)
