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
from z3.z3 import _symbol2py, _to_sort_ref

from . import config

FORMAT = "kdrag-proof-cache-2"
MAX_BYTES = 50_000_000
hits = 0
misses = 0

_dir: str | None = None
_secret = b""
_digests: set[str] = set()
_FRESH = re.compile(r"(.*)!([0-9]+)")


class Refuse(Exception):
    """The term contains something the hash does not cover."""


class _Table:
    """
    Number the distinct terms, sorts and declarations of a term in order of first visit.
    Each row holds strings, ints and the numbers of earlier rows, so the rows determine the term.
    Arguments are raw z3 pointers, memoized before wrapping them in z3py objects, which is slow.
    """

    def __init__(self, ctx: z3.Context):
        self.ctx = ctx
        self.rows: list[tuple] = []
        # Keyed by raw pointer, without incrementing reference counts. This is safe because every pointer
        # is a part of the term (or of a datatype definition, which z3 keeps), the caller keeps the term
        # alive during the walk, and the table is discarded afterwards. z3py wrappers count their own references.
        self.memo: dict[tuple[str, int], int] = {}
        self.fresh: dict[tuple, int] = {}

    def row(self, *entry) -> int:
        self.rows.append(entry)
        return len(self.rows) - 1

    def sort(self, ptr) -> int:
        """
        A sort is identified by its printed name, which includes its parameters (`(Array Int (_ BitVec 8))`).
        Datatypes also get a row with their definition. Component sorts are visited for their definitions.
        """
        if ("s", ptr.value) in self.memo:
            return self.memo["s", ptr.value]
        s = _to_sort_ref(ptr, self.ctx)
        # These sorts' names hide their parameters.
        if s.kind() in (
            z3.Z3_FINITE_DOMAIN_SORT,
            z3.Z3_RELATION_SORT,
            z3.Z3_UNKNOWN_SORT,
        ):
            raise Refuse("sort", s)
        # Memoized before visiting components, so recursive datatypes terminate.
        r = self.memo["s", ptr.value] = self.row("sort", s.kind(), s.sexpr())
        if isinstance(s, z3.ArraySortRef):
            for j in range(c.Z3_get_array_arity(s.ctx_ref(), ptr)):
                self.sort(s.domain_n(j).ast)
            self.sort(s.range().ast)
        elif isinstance(s, (z3.SeqSortRef, z3.ReSortRef)):
            self.sort(s.basis().ast)
        elif isinstance(s, z3.DatatypeSortRef):
            ctors = []
            for i in range(s.num_constructors()):
                accs = [s.accessor(i, j) for j in range(s.constructor(i).arity())]
                fields = tuple((a.name(), self.sort(a.range().ast)) for a in accs)
                ctors.append((s.constructor(i).name(), fields))
            self.row("datatype", r, tuple(ctors))
        return r

    def decl(self, ptr) -> int:
        """A declaration is identified by its kind, name, signature and parameters (`extract 3 0`)."""
        if ("d", ptr.value) in self.memo:
            return self.memo["d", ptr.value]
        ctx = self.ctx.ref()
        k = c.Z3_get_decl_kind(ctx, ptr)
        name = _symbol2py(self.ctx, c.Z3_get_decl_name(ctx, ptr))
        # Recursive definitions are not part of the term.
        if k in (z3.Z3_OP_RECURSIVE, z3.Z3_OP_INTERNAL):
            raise Refuse("declaration", name)
        n = c.Z3_get_domain_size(ctx, ptr)
        sig = [self.sort(c.Z3_get_domain(ctx, ptr, j)) for j in range(n)]
        sig.append(self.sort(c.Z3_get_range(ctx, ptr)))
        if k == z3.Z3_OP_UNINTERPRETED and isinstance(name, str):
            if m := _FRESH.fullmatch(name):
                i = self.fresh.setdefault((name, tuple(sig)), len(self.fresh))
                name = f"{m.group(1)}!{i}"
        params = []
        if c.Z3_get_decl_num_parameters(ctx, ptr):
            ps = z3.FuncDeclRef(ptr, self.ctx).params()
        else:
            ps = []
        for p in ps:
            if isinstance(p, z3.SortRef):
                params.append(("sort", self.sort(p.ast)))
            elif isinstance(p, z3.FuncDeclRef):
                params.append(("decl", self.decl(p.ast)))
            elif isinstance(p, z3.ExprRef):
                params.append(("term", self.term(p.as_ast())))
            elif p in ("internal parameter", "internal string"):
                # What z3py returns for opaque parameters.
                raise Refuse("parameter", name)
            else:
                # An int, a float, or a str for rationals and symbols.
                params.append(p)
        r = self.memo["d", ptr.value] = self.row(
            "decl", k, name, tuple(sig), tuple(params)
        )
        return r

    def term(self, e) -> int:
        if ("t", e.value) in self.memo:
            return self.memo["t", e.value]
        ctx = self.ctx.ref()
        k = c.Z3_get_ast_kind(ctx, e)
        if k == z3.Z3_APP_AST:
            d = c.Z3_get_app_decl(ctx, e)
            if c.Z3_get_decl_kind(ctx, d) == z3.Z3_OP_INTERNAL and c.Z3_is_string(
                ctx, e
            ):
                r = self.row("str", c.Z3_get_string(ctx, e))
            else:
                n = c.Z3_get_app_num_args(ctx, e)
                args = [self.term(c.Z3_get_app_arg(ctx, e, j)) for j in range(n)]
                r = self.row("app", self.decl(d), *args)
        elif k == z3.Z3_NUMERAL_AST:
            s = c.Z3_get_sort(ctx, e)
            if c.Z3_get_sort_kind(ctx, s) not in (
                z3.Z3_INT_SORT,
                z3.Z3_REAL_SORT,
                z3.Z3_BV_SORT,
            ):
                raise Refuse("numeral", k)
            r = self.row("num", c.Z3_get_numeral_string(ctx, e), self.sort(s))
        elif k == z3.Z3_VAR_AST:
            # A de Bruijn index.
            r = self.row(
                "var", c.Z3_get_index_value(ctx, e), self.sort(c.Z3_get_sort(ctx, e))
            )
        elif k == z3.Z3_QUANTIFIER_AST:
            # Bound names, patterns and weights are not hashed.
            q = z3.QuantifierRef(e, self.ctx)
            kind = (
                "lambda" if q.is_lambda() else "forall" if q.is_forall() else "exists"
            )
            vs = tuple(self.sort(q.var_sort(j).ast) for j in range(q.num_vars()))
            r = self.row(kind, vs, self.term(q.body().as_ast()))
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
    table = _Table(fml.ctx)
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
