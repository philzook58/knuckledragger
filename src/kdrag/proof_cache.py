"""
A persistent cache of z3 queries already proved unsat, used by `kernel.prove` when `config.cache` is set.
This module is part of the trusted kernel. Turn the cache off to recheck everything.

The key of a query `Implies(And(by), thm)` is a keyed hash of its structure, read directly from z3's AST
without printing. Each distinct term, sort and declaration becomes a node, numbered in order of first visit.
A node holds strings, ints and the numbers of its children, so the nodes determine the term. Not hashed: bound variable names (variables are de Bruijn
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

FORMAT = "kdrag-proof-cache-3"
MAX_BYTES = 50_000_000
hits = 0
misses = 0

_dir: str | None = None
_secret = b""
_digests: set[str] = set()
_FRESH = re.compile(r"(.*)!([0-9]+)")
# Sorts without component sorts. Their printed form includes their parameters (`(_ FloatingPoint 8 24)`).
_LEAF_SORTS = (
    z3.Z3_BOOL_SORT,
    z3.Z3_INT_SORT,
    z3.Z3_REAL_SORT,
    z3.Z3_CHAR_SORT,
    z3.Z3_ROUNDING_MODE_SORT,
    z3.Z3_BV_SORT,
    z3.Z3_FLOATING_POINT_SORT,
    z3.Z3_UNINTERPRETED_SORT,
)


class Refuse(Exception):
    """The term contains something the hash does not cover."""


class _Canonicalizer:
    """
    Number the distinct terms, sorts and declarations of a term in order of first visit.
    Each node holds strings, ints and the numbers of earlier nodes, so the nodes determine the term.
    """

    def __init__(self, ctx):
        self.ctx = ctx
        self.nodes: list[tuple] = []
        # Keyed by raw pointer, without incrementing reference counts. This is safe because every pointer
        # is a part of the term (or of a datatype definition, which z3 keeps), the caller keeps the term
        # alive during the walk, and the canonicalizer is discarded afterwards.
        self.memo: dict[tuple[str, int], int] = {}
        self.fresh: dict[tuple, int] = {}

    def node(self, *entry) -> int:
        self.nodes.append(entry)
        return len(self.nodes) - 1

    def symbol(self, sym) -> str | int:
        if c.Z3_get_symbol_kind(self.ctx, sym) == z3.Z3_INT_SYMBOL:
            return c.Z3_get_symbol_int(self.ctx, sym)
        return c.Z3_get_symbol_string(self.ctx, sym)

    def name(self, d) -> str | int:
        return self.symbol(c.Z3_get_decl_name(self.ctx, d))

    def sort(self, s) -> int:
        """
        A sort is identified by its kind, name, printed form (`(_ BitVec 8)`) and the nodes of its component sorts.
        Printed forms alone are ambiguous: the int symbol 3 and the string "k!3" both print as `k!3`.
        Datatypes also get a node with their definition. Sorts with parts we do not visit are refused.
        """
        if ("s", s.value) in self.memo:
            return self.memo["s", s.value]
        ctx = self.ctx
        k = c.Z3_get_sort_kind(ctx, s)
        name = self.symbol(c.Z3_get_sort_name(ctx, s))
        printed = c.Z3_sort_to_string(ctx, s)
        if k == z3.Z3_DATATYPE_SORT:
            # Memoized before visiting the fields, so recursive datatypes terminate.
            r = self.memo["s", s.value] = self.node("sort", k, name, printed)
            ctors = []
            for i in range(c.Z3_get_datatype_sort_num_constructors(ctx, s)):
                ctor = c.Z3_get_datatype_sort_constructor(ctx, s, i)
                n = c.Z3_get_domain_size(ctx, ctor)
                accs = [
                    c.Z3_get_datatype_sort_constructor_accessor(ctx, s, i, j)
                    for j in range(n)
                ]
                fields = tuple(
                    (self.name(a), self.sort(c.Z3_get_range(ctx, a))) for a in accs
                )
                ctors.append((self.name(ctor), fields))
            self.node("datatype", r, tuple(ctors))
            return r
        if k == z3.Z3_ARRAY_SORT:
            n = c.Z3_get_array_arity(ctx, s)
            parts = [
                self.sort(c.Z3_get_array_sort_domain_n(ctx, s, j)) for j in range(n)
            ]
            parts.append(self.sort(c.Z3_get_array_sort_range(ctx, s)))
        elif k == z3.Z3_SEQ_SORT:
            parts = [self.sort(c.Z3_get_seq_sort_basis(ctx, s))]
        elif k == z3.Z3_RE_SORT:
            parts = [self.sort(c.Z3_get_re_sort_basis(ctx, s))]
        elif k in _LEAF_SORTS:
            parts = []
        else:
            raise Refuse("sort", printed)
        # A parametric uninterpreted sort such as `(List Int)` has parts we do not visit.
        if k == z3.Z3_UNINTERPRETED_SORT and printed.startswith("("):
            raise Refuse("sort", printed)
        r = self.memo["s", s.value] = self.node("sort", k, name, printed, tuple(parts))
        return r

    def decl(self, d) -> int:
        """A declaration is identified by its kind, name, signature and parameters (`extract 3 0`)."""
        if ("d", d.value) in self.memo:
            return self.memo["d", d.value]
        ctx = self.ctx
        k, name = c.Z3_get_decl_kind(ctx, d), self.name(d)
        # Recursive definitions are not part of the term.
        if k in (z3.Z3_OP_RECURSIVE, z3.Z3_OP_INTERNAL):
            raise Refuse("declaration", name)
        sig = [
            self.sort(c.Z3_get_domain(ctx, d, j))
            for j in range(c.Z3_get_domain_size(ctx, d))
        ]
        sig.append(self.sort(c.Z3_get_range(ctx, d)))
        if k == z3.Z3_OP_UNINTERPRETED and isinstance(name, str):
            if m := _FRESH.fullmatch(name):
                i = self.fresh.setdefault((name, tuple(sig)), len(self.fresh))
                name = f"{m.group(1)}!{i}"
        params = []
        for j in range(c.Z3_get_decl_num_parameters(ctx, d)):
            pk = c.Z3_get_decl_parameter_kind(ctx, d, j)
            if pk == z3.Z3_PARAMETER_INT:
                params.append(("int", c.Z3_get_decl_int_parameter(ctx, d, j)))
            elif pk == z3.Z3_PARAMETER_RATIONAL:
                params.append(("rat", c.Z3_get_decl_rational_parameter(ctx, d, j)))
            elif pk == z3.Z3_PARAMETER_SYMBOL:
                sym = c.Z3_get_decl_symbol_parameter(ctx, d, j)
                params.append(("sym", c.Z3_get_symbol_string(ctx, sym)))
            elif pk == z3.Z3_PARAMETER_SORT:
                params.append(
                    ("sort", self.sort(c.Z3_get_decl_sort_parameter(ctx, d, j)))
                )
            elif pk == z3.Z3_PARAMETER_FUNC_DECL:
                params.append(
                    ("decl", self.decl(c.Z3_get_decl_func_decl_parameter(ctx, d, j)))
                )
            elif pk == z3.Z3_PARAMETER_AST:
                params.append(
                    ("term", self.term(c.Z3_get_decl_ast_parameter(ctx, d, j)))
                )
            else:
                raise Refuse("parameter", name)
        r = self.memo["d", d.value] = self.node(
            "decl", k, name, tuple(sig), tuple(params)
        )
        return r

    def term(self, e) -> int:
        if ("t", e.value) in self.memo:
            return self.memo["t", e.value]
        ctx = self.ctx
        k = c.Z3_get_ast_kind(ctx, e)
        if k == z3.Z3_APP_AST:
            d = c.Z3_get_app_decl(ctx, e)
            if c.Z3_get_decl_kind(ctx, d) == z3.Z3_OP_INTERNAL and c.Z3_is_string(
                ctx, e
            ):
                r = self.node("str", c.Z3_get_string(ctx, e))
            else:
                n = c.Z3_get_app_num_args(ctx, e)
                args = [self.term(c.Z3_get_app_arg(ctx, e, j)) for j in range(n)]
                r = self.node("app", self.decl(d), *args)
        elif k == z3.Z3_NUMERAL_AST:
            s = c.Z3_get_sort(ctx, e)
            if c.Z3_get_sort_kind(ctx, s) not in (
                z3.Z3_INT_SORT,
                z3.Z3_REAL_SORT,
                z3.Z3_BV_SORT,
            ):
                raise Refuse("numeral", k)
            r = self.node("num", c.Z3_get_numeral_string(ctx, e), self.sort(s))
        elif k == z3.Z3_VAR_AST:
            # A de Bruijn index.
            r = self.node(
                "var", c.Z3_get_index_value(ctx, e), self.sort(c.Z3_get_sort(ctx, e))
            )
        elif k == z3.Z3_QUANTIFIER_AST:
            # Bound names, patterns and weights are not hashed.
            if c.Z3_is_lambda(ctx, e):
                q = "lambda"
            else:
                q = "forall" if c.Z3_is_quantifier_forall(ctx, e) else "exists"
            n = c.Z3_get_quantifier_num_bound(ctx, e)
            vs = tuple(
                self.sort(c.Z3_get_quantifier_bound_sort(ctx, e, j)) for j in range(n)
            )
            r = self.node(q, vs, self.term(c.Z3_get_quantifier_body(ctx, e)))
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
    canon = _Canonicalizer(fml.ctx_ref())
    try:
        canon.term(fml.as_ast())
    except (Refuse, z3.Z3Exception):  # z3 errors mean we misread the term
        return None
    h = hashlib.blake2b(key=_secret, digest_size=32)
    h.update(f"{FORMAT}\n{z3.get_full_version()}\n{canon.nodes!r}".encode())
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
