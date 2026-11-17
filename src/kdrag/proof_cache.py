"""
A persistent cache of z3 queries already proved unsat, used by `kernel.prove` when `config.cache` is set.
This module is part of the trusted kernel. Turn the cache off to recheck everything.

The key of a query `Implies(And(by), thm)` is a keyed hash of its structure, read directly from z3's AST
without printing. Each distinct node gets a row in a table, whose entries are strings, ints and the row numbers
of its children, so the table determines the term. Not hashed: bound variable names (variables are de Bruijn
indices), quantifier patterns and weights (they do not change satisfiability), and the numbers of fresh names
`x!12`, which are renumbered in order of first occurrence. Equal keys therefore mean equal queries up to
alpha-renaming and a bijective renaming of fresh names, which preserves unsat.
Uninterpreted declarations are identified by name and signature, which is how z3 identifies them,
so `Int x` and `Real x` stay distinct. Anything not understood (such as `RecFunction`) is never cached.

The hash is keyed by a random secret in `config.cache_dir`, so a copied or edited cache file only causes misses.
"""

import hashlib
import os
import re

import z3
from z3 import z3core as c

from . import config

FORMAT = "kdrag-proof-cache-2"
MAX_BYTES = 50_000_000
hits = 0
misses = 0

_dir: str | None = None
_secret = b""
_digests: set[str] = set()
_FRESH = re.compile(r"(.*)!([0-9]+)")
_SIMPLE_SORTS = (
    z3.Z3_BOOL_SORT,
    z3.Z3_INT_SORT,
    z3.Z3_REAL_SORT,
    z3.Z3_CHAR_SORT,
    z3.Z3_ROUNDING_MODE_SORT,
)


class Refuse(Exception):
    """The term contains something the hash does not cover."""


class _Table:
    """Number the distinct nodes, sorts and declarations of a term in order of first visit."""

    def __init__(self, ctx):
        self.ctx = ctx
        self.rows: list[tuple] = []
        self.memo: dict[
            tuple[str, int], int
        ] = {}  # keyed by pointer, unique while the term is alive
        self.fresh: dict[tuple, int] = {}
        self.datatypes: list[
            int
        ] = []  # datatype sorts being visited, for recursive references

    def row(self, *entry) -> int:
        self.rows.append(entry)
        return len(self.rows) - 1

    def name(self, sym) -> str:
        if c.Z3_get_symbol_kind(self.ctx, sym) == z3.Z3_INT_SYMBOL:
            return "#" + str(c.Z3_get_symbol_int(self.ctx, sym))
        return c.Z3_get_symbol_string(self.ctx, sym)

    def sort(self, s) -> int:
        ctx = self.ctx
        if ("s", s.value) in self.memo:
            return self.memo["s", s.value]
        if (
            s.value in self.datatypes
        ):  # recursive occurrence: refer to the enclosing datatype by depth
            return self.row("rec", len(self.datatypes) - self.datatypes.index(s.value))
        k = c.Z3_get_sort_kind(ctx, s)
        if k in _SIMPLE_SORTS:
            r = self.row("s", k)
        elif k == z3.Z3_UNINTERPRETED_SORT:
            r = self.row("s", k, self.name(c.Z3_get_sort_name(ctx, s)))
        elif k == z3.Z3_BV_SORT:
            r = self.row("s", k, c.Z3_get_bv_sort_size(ctx, s))
        elif k == z3.Z3_ARRAY_SORT:
            dom = [
                c.Z3_get_array_sort_domain_n(ctx, s, j)
                for j in range(c.Z3_get_array_arity(ctx, s))
            ]
            r = self.row(
                "s",
                k,
                *map(self.sort, dom),
                self.sort(c.Z3_get_array_sort_range(ctx, s)),
            )
        elif k == z3.Z3_SEQ_SORT:
            r = self.row("s", k, self.sort(c.Z3_get_seq_sort_basis(ctx, s)))
        elif k == z3.Z3_RE_SORT:
            r = self.row("s", k, self.sort(c.Z3_get_re_sort_basis(ctx, s)))
        elif k == z3.Z3_DATATYPE_SORT:
            self.datatypes.append(s.value)
            ctors = []
            for i in range(c.Z3_get_datatype_sort_num_constructors(ctx, s)):
                ctor = c.Z3_get_datatype_sort_constructor(ctx, s, i)
                n = c.Z3_get_domain_size(ctx, ctor)
                accs = [
                    c.Z3_get_datatype_sort_constructor_accessor(ctx, s, i, j)
                    for j in range(n)
                ]
                fields = tuple(
                    (
                        self.name(c.Z3_get_decl_name(ctx, a)),
                        self.sort(c.Z3_get_range(ctx, a)),
                    )
                    for a in accs
                )
                ctors.append((self.name(c.Z3_get_decl_name(ctx, ctor)), fields))
            self.datatypes.pop()
            r = self.row("s", k, self.name(c.Z3_get_sort_name(ctx, s)), tuple(ctors))
            if (
                self.datatypes
            ):  # may refer to enclosing datatypes by depth, so do not memoize
                return r
        else:
            raise Refuse("sort", k)
        self.memo["s", s.value] = r
        return r

    def decl(self, d) -> int:
        ctx = self.ctx
        if ("d", d.value) in self.memo:
            return self.memo["d", d.value]
        k = c.Z3_get_decl_kind(ctx, d)
        if k in (
            z3.Z3_OP_RECURSIVE,
            z3.Z3_OP_INTERNAL,
        ):  # recursive definitions are not part of the term
            raise Refuse("declaration", k)
        dom = [c.Z3_get_domain(ctx, d, j) for j in range(c.Z3_get_domain_size(ctx, d))]
        sig = (tuple(map(self.sort, dom)), self.sort(c.Z3_get_range(ctx, d)))
        name = self.name(c.Z3_get_decl_name(ctx, d))
        params = []
        for j in range(c.Z3_get_decl_num_parameters(ctx, d)):
            pk = c.Z3_get_decl_parameter_kind(ctx, d, j)
            if pk == z3.Z3_PARAMETER_INT:
                params.append(("i", c.Z3_get_decl_int_parameter(ctx, d, j)))
            elif pk == z3.Z3_PARAMETER_RATIONAL:
                params.append(("q", c.Z3_get_decl_rational_parameter(ctx, d, j)))
            elif pk == z3.Z3_PARAMETER_SYMBOL:
                params.append(
                    ("y", self.name(c.Z3_get_decl_symbol_parameter(ctx, d, j)))
                )
            elif pk == z3.Z3_PARAMETER_SORT:
                params.append(("s", self.sort(c.Z3_get_decl_sort_parameter(ctx, d, j))))
            elif pk == z3.Z3_PARAMETER_FUNC_DECL:
                params.append(
                    ("f", self.decl(c.Z3_get_decl_func_decl_parameter(ctx, d, j)))
                )
            else:
                raise Refuse("parameter", pk)
        if k == z3.Z3_OP_UNINTERPRETED and (m := _FRESH.fullmatch(name)):
            name = (
                m.group(1)
                + "!"
                + str(self.fresh.setdefault((name, sig), len(self.fresh)))
            )
        r = self.row("d", k, name, sig, tuple(params))
        self.memo["d", d.value] = r
        return r

    def term(self, e) -> int:
        ctx = self.ctx
        if ("t", e.value) in self.memo:
            return self.memo["t", e.value]
        k = c.Z3_get_ast_kind(ctx, e)
        if k == z3.Z3_APP_AST:
            d = c.Z3_get_app_decl(ctx, e)
            if c.Z3_get_decl_kind(ctx, d) == z3.Z3_OP_INTERNAL and c.Z3_is_string(
                ctx, e
            ):
                r = self.row("str", c.Z3_get_string(ctx, e))
            else:
                args = [
                    c.Z3_get_app_arg(ctx, e, j)
                    for j in range(c.Z3_get_app_num_args(ctx, e))
                ]
                r = self.row("a", self.decl(d), *map(self.term, args))
        elif k == z3.Z3_NUMERAL_AST:
            s = c.Z3_get_sort(ctx, e)
            if c.Z3_get_sort_kind(ctx, s) not in (
                z3.Z3_INT_SORT,
                z3.Z3_REAL_SORT,
                z3.Z3_BV_SORT,
            ):
                raise Refuse("numeral")
            r = self.row("n", c.Z3_get_numeral_string(ctx, e), self.sort(s))
        elif k == z3.Z3_VAR_AST:
            r = self.row(
                "v", c.Z3_get_index_value(ctx, e), self.sort(c.Z3_get_sort(ctx, e))
            )
        elif k == z3.Z3_QUANTIFIER_AST:
            q = (
                "lambda"
                if c.Z3_is_lambda(ctx, e)
                else "forall"
                if c.Z3_is_quantifier_forall(ctx, e)
                else "exists"
            )
            n = c.Z3_get_quantifier_num_bound(ctx, e)
            vs = tuple(
                self.sort(c.Z3_get_quantifier_bound_sort(ctx, e, j)) for j in range(n)
            )
            r = self.row("q", q, vs, self.term(c.Z3_get_quantifier_body(ctx, e)))
        else:
            raise Refuse("ast", k)
        self.memo["t", e.value] = r
        return r


def _load():
    """Load the secret and the digests of `config.cache_dir`, creating them if needed."""
    global _dir, _secret, _digests
    os.makedirs(config.cache_dir, exist_ok=True)
    secret_path = os.path.join(config.cache_dir, "secret")
    if not os.path.exists(secret_path):
        tmp = f"{secret_path}.{os.getpid()}"
        with open(
            os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600), "wb"
        ) as f:
            f.write(os.urandom(32))
        try:
            os.link(tmp, secret_path)  # atomic: another process may have won the race
        except FileExistsError:
            pass
        os.unlink(tmp)
    with open(secret_path, "rb") as f:
        _secret = f.read()
    if len(_secret) != 32:
        raise ValueError(
            "Corrupt proof cache secret. Delete it to start over", secret_path
        )
    path = os.path.join(config.cache_dir, "proofs.txt")
    if os.path.exists(path) and os.path.getsize(path) > MAX_BYTES:
        os.unlink(path)
    try:
        with open(path) as f:
            _digests = {line for line in f.read().split() if len(line) == 64}
    except FileNotFoundError:
        _digests = set()
    _dir = config.cache_dir


def key(fml: z3.BoolRef) -> str | None:
    """The cache key of `fml`, or None if it contains something the hash does not cover."""
    if _dir != config.cache_dir:
        _load()
    table = _Table(fml.ctx_ref())
    try:
        table.term(fml.as_ast())
    except Refuse:
        return None
    h = hashlib.blake2b(key=_secret, digest_size=32)
    h.update(f"{FORMAT}\n{z3.get_full_version()}\n{table.rows!r}".encode())
    return h.hexdigest()


def lookup(k: str) -> bool:
    global hits, misses
    if k in _digests:
        hits += 1
        return True
    misses += 1
    return False


def record(k: str):
    """Record that the query with key `k` is unsat."""
    _digests.add(k)
    path = os.path.join(config.cache_dir, "proofs.txt")
    fd = os.open(path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        os.write(
            fd, (k + "\n").encode()
        )  # one short append is atomic, so concurrent writers are safe
    finally:
        os.close(fd)


def clear():
    """Delete the cached digests of `config.cache_dir`."""
    global _dir
    path = os.path.join(config.cache_dir, "proofs.txt")
    if os.path.exists(path):
        os.unlink(path)
    _dir = None
