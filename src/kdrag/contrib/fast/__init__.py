"""
Experiments in C FFI
"""

from cffi import FFI
import tempfile
import sys
from pathlib import Path
import z3

# import time
# start = time.time()
ffibuilder = FFI()

ffibuilder.cdef("""
int myadd(int a, int b);
const char* z3_version();
typedef struct _Z3_config *Z3_config;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_ast *Z3_ast;
typedef struct _Z3_ast_vector *Z3_ast_vector;
Z3_ast my_mk_true(Z3_context ctx);
Z3_ast my_mk_and(Z3_context ctx, Z3_ast a, Z3_ast b);
Z3_ast_vector KDRAG_get_consts(Z3_context ctx, Z3_ast t);
""")
assert z3.__file__ is not None
z3lib = Path(z3.__file__).parent.absolute() / "lib"
z3_include = Path(z3.__file__).parent.absolute() / "include"
ffibuilder.set_source(
    "_fast",
    (Path(__file__).parent / "fast.c").read_text(),
    library_dirs=[str(z3lib)],
    include_dirs=[str(z3_include)],
    libraries=["z3"],
)
# Build outside the source tree without changing the process working directory.
tmpdir = tempfile.mkdtemp()
ffibuilder.compile(tmpdir=tmpdir, verbose=True)
sys.path.insert(1, tmpdir)

from _fast.lib import *  # noqa: E402, F403  # type: ignore

# assert False, time.time() - start # 0.25s


def ctxptr(ctx: z3.Context):
    ptr = ctx.ref()
    assert ptr is not None
    return ffibuilder.cast("void *", ptr.value)


def astptr(ast: z3.AstRef):
    return ffibuilder.cast("void *", ast.as_ast().value)


def intify(ptr):
    return int(ffibuilder.cast("uintptr_t", ptr))


def test():
    """
    >>> myadd(2, 3)
    5
    >>> ctx = ffibuilder.cast("void *", z3.main_ctx().ctx.value)
    >>> ast = my_mk_true(ctx)
    >>> value = intify(ast)
    >>> z3.BoolRef(value)
    True
    >>> z3.BoolRef(intify(my_mk_and(ctx, ast, ast)))
    And(True, True)
    >>> z3.AstVector(intify(KDRAG_get_consts(ctx, ast)), z3.main_ctx())
    [True]
    >>> x = z3.Int("x")
    >>> z3.AstVector(intify(KDRAG_get_consts(ctx, astptr(x + x + x))), z3.main_ctx())
    [x]
    """

    # >>> intify(my_mk_and(ctx, ast, ast))
    # >>> FFI().string(z3_version())
    # >>> my_mk_true(ffibuilder.cast("Z3_context", z3.main_ctx().ctx.value))
