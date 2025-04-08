import kdrag.smt as smt
import kdrag as kd
import re

import subprocess
import tempfile
import os
import cffi


def ctype_of_sort(s: smt.SortRef):
    if s == smt.BoolSort():
        return "bool"
    if isinstance(s, smt.BitVecSortRef):
        if s.size() in [8, 16, 32, 64]:
            return f"uint{s.size()}_t"
        else:
            raise NotImplementedError("No support for arbitrary C int sizes", s.size())
    else:
        raise NotImplementedError(f"Cannot convert {s} to C type")


# Regex pattern for valid C identifiers
c_identifier_regex = r"^[A-Za-z_][A-Za-z0-9_]*$"


# Function to check if a given string is a valid C identifier
def is_valid_c_identifier(identifier: str) -> bool:
    return bool(re.match(c_identifier_regex, identifier))


# List of C keywords (C11 standard)
c_keywords = {
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "register",
    "restrict",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",
    "_Alignas",
    "_Alignof",
    "_Atomic",
    "_Bool",
    "_Complex",
    "_Generic",
    "_Imaginary",
    "_Noreturn",
    "_Static_assert",
    "_Thread_local",
}


# Function to check valid C identifier considering keywords
def is_valid_c_identifier_strict(identifier: str) -> bool:
    return is_valid_c_identifier(identifier) and identifier not in c_keywords


binops = {
    "bvadd": "+",
    "bvsub": "-",
    "bvmul": "*",
}

comp = {
    "bvuge": ">=",
    "bvult": "<",
    "bvule": "<=",
    "bvugt": ">",
}


def c_of_expr(
    ctx: list[smt.ExprRef], sig: list[smt.FuncDeclRef], e: smt.ExprRef
) -> str:
    ctype_of_sort(e.sort())  # check sort is supported
    if any(e.eq(c) for c in ctx):
        assert is_valid_c_identifier_strict(e.decl().name())
        return e.decl().name()
    elif smt.is_app(e):
        decl = e.decl()
        decl_name = decl.name()
        children = [c_of_expr(ctx, sig, c) for c in e.children()]
        assert all(isinstance(c, str) for c in children)
        nargs = len(children)
        if e.decl() in sig:
            assert is_valid_c_identifier_strict(e.decl().name())
            return f"""{e.decl().name()}({", ".join(children)})"""
        elif smt.is_if(e):
            return f"({children[0]} ? {children[1]} : {children[2]})"
        elif isinstance(e, smt.BoolRef):
            if smt.is_true(e):
                return "true"
            elif smt.is_false(e):
                return "false"
            elif smt.is_and(e):
                return f"({' && '.join(children)})"
            elif smt.is_or(e):
                return f"({' || '.join(children)})"
            elif smt.is_not(e):
                assert nargs == 1
                return f"(!{children[0]})"
            elif decl_name in comp:
                assert nargs == 2
                return f"({children[0]} {comp[decl_name]} {c_of_expr(ctx, sig, e.children()[1])})"
            elif decl_name in ["bvsge", "bvslt", "bvsle", "bvsgt"]:
                raise NotImplementedError("Signed comparison not supported", e)
            else:
                raise NotImplementedError("Unsupported boolean expression", e)
        elif isinstance(e, smt.BitVecRef):
            if isinstance(e, smt.BitVecNumRef):
                return "0b" + e.as_binary_string()
            elif nargs == 1:
                if decl_name == "bvnot":
                    return f"(~{children[0]})"
                elif decl_name == "bvneg":
                    return f"(-{children[0]})"
                else:
                    raise NotImplementedError(
                        f"Unsupported unary operation: {decl_name}"
                    )
            if nargs == 2:
                op = binops.get(decl_name)
                if op is not None:
                    return f"({children[0]} {op} {children[1]})"
                elif decl_name in ["|", "&", "^"]:
                    return f"({children[0]} {decl_name} {children[1]})"
                else:
                    raise NotImplementedError(
                        f"Unsupported binary operation: {decl_name}"
                    )
            else:
                raise NotImplementedError(
                    f"Unsupported bitvector operation with {nargs} arguments: {decl_name}"
                )
        else:
            raise NotImplementedError(f"Unsupported expression type: {e}")
        # TODO: floats
    else:
        raise NotImplementedError(f"Unsupported expression type: {e}")


def cstring(name, args, body):
    assert is_valid_c_identifier_strict(name)
    assert all(is_valid_c_identifier_strict(arg.decl().name()) for arg in args)
    assert all(smt.is_const(arg) for arg in args)
    decl = smt.Function("name", *([arg.sort() for arg in args] + [body.sort()]))
    return f"""\
#include <stdint.h>
#include <stdbool.h>
{ctype_of_sort(body.sort())} {name}({', '.join([f"{ctype_of_sort(arg.sort())} {arg.decl().name()}" for arg in args])}){{
    return {c_of_expr(args, [decl], body)};
}}
"""


def of_defn(f: smt.FuncDeclRef):
    defn = kd.kernel.defns[f]
    return cstring(defn.name, defn.args, defn.body)


def compile_c(c_code, opts=[]):
    """
    #>>> x,y = smt.BitVecs("x y", 32)
    #>>> compile_c(cstring("foo", [x,y], smt.If(smt.UGT(x + x*y + 1, x), x , y)))
    """
    tmpdir = (
        tempfile.mkdtemp()
    )  # with tempfile.TemporaryDirectory(delete=False) as tmpdir:
    c_file = os.path.join(tmpdir, "temp.c")
    so_file = os.path.join(tmpdir, "temp.so")

    with open(c_file, "w") as f:
        f.write(c_code)

    # Compile C code into a shared object
    subprocess.run(
        [
            "gcc",
            "-Wall",
            "-Wextra",
            "-Wconversion",
            "-Warith-conversion",
            "-Werror",
            "-shared",
            "-fPIC",
            c_file,
            "-o",
            so_file,
        ]
        + opts,
        check=True,
        capture_output=True,
    )
    return so_file


def link(name, args, body, filename):
    ffi = cffi.FFI()
    ffi.cdef(f"""\
    {ctype_of_sort(body.sort())} {name}({', '.join([f"{ctype_of_sort(arg.sort())}" for arg in args])});
    """)
    lib = ffi.dlopen(filename)
    return lib


def compile_and_link(name, args, body):
    so_file = compile_c(cstring(name, args, body))
    return link(name, args, body, so_file)


def compile_and_link_defn(f: smt.FuncDeclRef):
    defn = kd.kernel.defns[f]
    return compile_and_link(defn.name, defn.args, defn.body)
