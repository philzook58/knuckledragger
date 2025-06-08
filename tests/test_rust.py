
from kdrag.printers.rust import init_proj, compile_rust, default_dir
import shutil
import pytest

@pytest.mark.slow
def test_rust():
    try:
        shutil.rmtree("/tmp/kdrag_rust")
    except FileNotFoundError:
        pass
    init_proj()
    mymod = compile_rust("myadd", "fn myadd(x: i64, y: i64) -> i64 { x + y }")
    assert mymod.myadd(3, 4) == 7

    