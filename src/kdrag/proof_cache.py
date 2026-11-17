"""
A persistent cache of z3 queries already proved unsat, used by `kernel.prove` when `config.cache` is set.
This module is part of the trusted kernel. Turn the cache off to recheck everything.

The key of a query `Implies(And(by), thm)` is a keyed hash of its SMT-LIB text, with let names (`?x12`)
and fresh names (`x!12`) renumbered in order of first occurrence across the whole query.
That is a bijective renaming of the query's own symbols, so equal keys mean equisatisfiable queries
as long as the printed text is unambiguous.
The printer introduces lets for subterms with several references (including Python's), so the same query
can print differently and miss. That costs hits, never soundness.
z3 prints symbols by name only, so overloaded symbols (`Int x` and `Real x`, two datatypes with a `nil`,
a user `abs`) and captured variables print identically. Such queries are never cached (see `ambiguous`).

The hash is keyed by a random secret in `config.cache_dir`, so a copied or edited cache file only causes misses.
"""

import hashlib
import os
import re

import z3

from . import config

FORMAT = "kdrag-proof-cache-1"
MAX_BYTES = 50_000_000
hits = 0
misses = 0

# Builtin names from z3's `builtin_name("...")` tables and reserved words.
# Dotted builtins (`seq.len`, `fp.add`, ...) are covered by their prefixes instead.
BUILTIN_PREFIXES = frozenset(
    {"seq", "str", "re", "char", "fp", "ff", "complex", "int", "set", "pb"}
)
_BUILTIN_NAMES = """
    _ - ! * ** / && ^ + +oo +zero < <= = => -> > >= || ~ /0 abs acos acosh and arctan2
    array-ext as as-array asin asinh atan atan2 atanh atom bit0 bit1 bit2bool BitVec
    bool Bool bv bv2int bv2nat bvadd bvand bvashr bvcomp bvlshr bvmul bvnand bvneg
    bvnego bvnor bvnot bvor bvredand bvredor bvsaddo bvsdiv bvsdiv0 bvsdiv_i bvsdivo
    bvsge bvsgt bvshl bvsle bvslt bvsmod bvsmod0 bvsmod_i bvsmul_noovfl bvsmul_noudfl
    bvsmulo bvsrem bvsrem0 bvsrem_i bvssubo bvsub bvuaddo bvudiv bvudiv0 bvudiv_i bvuge
    bvugt bvule bvult bvumul_noovfl bvumulo bvurem bvurem0 bvurem_i bvusubo bvxnor
    bvxor card case-def cell char Char choice complement Complex concat cons const cos
    cosh default distinct div div0 divisible equals equiv euler exists exp extract
    ext_rotate_left ext_rotate_right false FiniteField FiniteSet Float128 Float16
    Float32 Float64 FloatingPoint forall fp if iff if_then_else implies Int int2bv
    intersection int_to_bv is is_int ite lambda let ln log map match mkbv mod mod0 NaN
    nil not -oo or par pi Proof Real recfun-num-rounds RegEx RegLan rem repeat RNA RNE
    rotate_left rotate_right RoundingMode roundNearestTiesToAway roundNearestTiesToEven
    roundTowardNegative roundTowardPositive roundTowardZero RTN RTP RTZ sbv_to_int
    select Seq Set set-has-size setminus sign_extend sin sinh store String
    StringSequence subset tan tanh to_fp to_fp_unsigned to_ieee_bv to_int to_real true
    ubv_to_int Unicode union update-field xor -zero zero_extend
"""
BUILTINS = frozenset(_BUILTIN_NAMES.split())

_SYM = r'[^\s()|";]'
# Strings, quoted symbols and comments are matched first so their contents are never renamed.
# The renamed tokens are whole symbols: let names `?x12`/`$x12` and fresh names `x!12` (not keywords `:k!1`).
_RENAME = re.compile(
    rf'"(?:[^"]|"")*"|\|[^|]*\||;[^\n]*|(?<!{_SYM})(?:[?$]x\d+|(?!:){_SYM}*![0-9]+)(?!{_SYM})'
)
_TOKEN = re.compile(rf"\|[^|]*\||[()]|{_SYM}+")
_LET = re.compile(r"[?$]x\d+")

_dir: str | None = None
_secret = b""
_digests: set[str] = set()


def canon(text: str) -> str:
    """
    Renumber let names and fresh names in order of first occurrence.

    >>> canon('(declare-fun x!7 () Int) (assert (let ((?x41 (f x!7 y!3))) (= ?x41 "x!7")))')
    '(declare-fun x!0 () Int) (assert (let ((?x1 (f x!0 y!2))) (= ?x1 "x!7")))'
    """
    names: dict[str, str] = {}

    def rename(m: re.Match) -> str:
        t = m.group(0)
        if t[0] in '"|;':
            return t
        if t not in names:
            prefix = t[:2] if t[0] in "?$" else t[: t.rindex("!") + 1]
            names[t] = prefix + str(len(names))
        return names[t]

    return _RENAME.sub(rename, text)


def _read(text: str) -> list:
    """Read SMT-LIB text into nested lists. Quoted symbols lose their bars and comments are dropped."""
    stack: list[list] = [[]]
    for t in _TOKEN.findall(text):
        if t == "(":
            stack.append([])
        elif t == ")":
            sexp = stack.pop()
            stack[-1].append(sexp)
        elif t[0] != ";":
            stack[-1].append(t.strip("|"))
    return stack[0]


def _reserved(name: str) -> bool:
    return (
        name in BUILTINS
        or ("." in name and name.partition(".")[0] in BUILTIN_PREFIXES)
        or _LET.fullmatch(name) is not None  # would clash with the printer's let names
    )


def declared(cmds: list) -> list[str] | None:
    """
    Names declared by the commands, or None for a command we do not recognize.

    >>> declared(_read("(declare-datatypes ((N 0)) (((z) (s (p N))))) (declare-fun f (N) Int) (assert true)"))
    ['N', 'z', 'is-z', 's', 'is-s', 'p', 'f']
    """
    names = []
    for cmd in cmds:
        match cmd:
            case ["declare-fun" | "declare-const" | "declare-sort", name, *_]:
                names.append(name)
            case ["declare-datatypes", dts, bodies]:
                names += [dt[0] for dt in dts]
                for body in bodies:
                    if body[0] == "par":
                        body = body[2]
                    for ctor in body:
                        names += [ctor[0], "is-" + ctor[0]] + [
                            acc[0] for acc in ctor[1:]
                        ]
            case ["define-funs-rec", sigs, _]:
                names += [sig[0] for sig in sigs]
            case ["set-info", *_] | ["assert", _] | ["check-sat"]:
                pass
            case _:
                return None
    return names


def ambiguous(text: str) -> bool:
    """
    Whether z3's printed query may denote more than one formula. z3 prints by name only, so this is the case when
    a name is declared twice or is a builtin, or a bound variable shadows a declared name, a builtin or an enclosing
    binder (instantiating `ForAll y, ForAll x, R(x, y)` with a constant `x` prints like `ForAll x, R(x, x)`).

    >>> ambiguous("(declare-fun x () Int) (assert (forall ((x Int)) (R x x)))")
    True
    >>> ambiguous("(declare-fun y () Int) (assert (and (forall ((x Int)) (> x y)) (exists ((x Int)) (= x y))))")
    False
    """
    cmds = _read(text)
    names = declared(cmds)
    if names is None or len(set(names)) != len(names) or any(map(_reserved, names)):
        return True
    todo = [(cmd, frozenset(names)) for cmd in cmds]
    while todo:
        e, scope = todo.pop()
        if isinstance(e, list) and e:
            if e[0] in ("forall", "exists", "lambda"):
                vs = [v[0] for v in e[1]]
                if len(set(vs)) != len(vs) or scope.intersection(vs):
                    return True
                if any(map(_reserved, vs)):
                    return True
                scope = scope.union(vs)
            elif e[0] == "match":  # binds pattern variables, which we do not track
                return True
            todo.extend((c, scope) for c in e)
    return False


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
    """The cache key of `fml`, or None if its printed form may be ambiguous."""
    if _dir != config.cache_dir:
        _load()
    text = z3.Z3_benchmark_to_smtlib_string(
        fml.ctx_ref(), "", "", "unknown", "", 0, (z3.Ast * 1)(), fml.as_ast()
    )
    try:
        if ambiguous(text):
            return None
    except (IndexError, TypeError):  # unexpected shape
        return None
    h = hashlib.blake2b(key=_secret, digest_size=32)
    h.update(f"{FORMAT}\n{z3.get_full_version()}\n{canon(text)}".encode())
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
