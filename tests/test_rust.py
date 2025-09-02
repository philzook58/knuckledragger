
from kdrag.printers.rust import init_proj, compile_rust, default_dir
import shutil
import pytest

import os
# https://github.com/prove-rs/z3.rs/tree/master/z3-sys
import z3

# Doesn't seem to work.
# s.environ.get('LD_LIBRARY_PATH', '') + ':' + 
#os.environ['LD_LIBRARY_PATH'] = os.path.join(os.path.dirname(z3.__file__), 'lib')
#os.environ["Z3_LIBRARY_PATH_OVERRIDE"] = so_path = os.path.join(os.path.dirname(z3.__file__), "lib")

import kdragrs
"""
print(open("/proc/self/maps").read())
print(os.path.join(os.path.dirname(z3.__file__), "lib"))

# Shows Two libz3 being loaded. Hmm.
"""

def test_myadd():
    assert kdragrs.myadd(3, 4) == 7


def test_id():
    x = z3.Int('x')
    #serial = x.serialize()
    x1 = kdragrs.my_id(x + 1)
    assert x1.eq(x + 1)

@pytest.mark.slow
def test_rust():
    try:
        shutil.rmtree("/tmp/kdrag_rust")
    except FileNotFoundError:
        pass
    init_proj()
    mymod = compile_rust("myadd", "fn myadd(x: i64, y: i64) -> i64 { x + y }")
    assert mymod.myadd(3, 4) == 7

