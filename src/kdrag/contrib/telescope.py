"""Experimental ordered contexts, backed by existing closed kernel proofs.

No FreshVar registry or new trusted rules. All-variable transports compile
through the old kernel's Herbrand and instantiation rules. Mixed-context
certificates currently use Z3; this is an API prototype.
ScopedExpr carries the same contexts through terms and Boolean propositions;
raw Z3 calls cross an explicit lift boundary, rather than silently losing scope.
"""

import operator as op
from dataclasses import dataclass, field
from typing import Callable, Sequence, overload

import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag.utils as utils


@dataclass(frozen=True, eq=False)
class Vars:
    """One simultaneous universal-quantifier block."""

    vs: tuple[smt.ExprRef, ...]


@dataclass(frozen=True, eq=False)
class Hyp:
    """One implication premise; use an explicit And to group premises."""

    thm: smt.BoolRef


def _absent(vs: Sequence[smt.ExprRef], thm: smt.ExprRef) -> bool:
    return not vs or utils.free_in(list(vs), thm)


@dataclass(frozen=True, eq=False)
class Context:
    """A checked telescope prefix. Extension validates only its new entry."""

    parent: "Context | None" = field(default=None, repr=False)
    entry: Vars | Hyp | None = field(default=None, repr=False)
    entries: tuple[Vars | Hyp, ...] = field(init=False)
    bound: tuple[smt.ExprRef, ...] = field(init=False, repr=False)
    hyps: tuple[smt.BoolRef, ...] = field(init=False, repr=False)
    bound_ids: frozenset[int] = field(init=False, repr=False)

    def __post_init__(self):
        if self.parent is None:
            if self.entry is not None:
                raise ValueError("An entry requires a checked parent context")
            entries, bound, hyps, ids = (), (), (), frozenset()
        else:
            _require_context(self.parent)
            entry = self.entry
            bound, hyps = self.parent.bound, self.parent.hyps
            ids = self.parent.bound_ids
            if isinstance(entry, Vars):
                if not isinstance(entry.vs, tuple) or not entry.vs:
                    raise ValueError("Vars requires a nonempty tuple")
                if not all(smt.is_const(v) and smt.is_uninterp(v) for v in entry.vs):
                    raise ValueError("Binders must be uninterpreted constants")
                added = frozenset(v.get_id() for v in entry.vs)
                if len(added) != len(entry.vs) or added & ids:
                    raise ValueError("Context binders must be distinct")
                bound, ids = bound + entry.vs, ids | added
                if any(not _absent(entry.vs, h) for h in hyps):
                    raise ValueError("Hypothesis refers to a later context variable")
            elif isinstance(entry, Hyp) and isinstance(entry.thm, smt.BoolRef):
                hyps = hyps + (entry.thm,)
            else:
                raise TypeError("Context entries must be Vars or Boolean Hyp entries")
            entries = self.parent.entries + (entry,)
        object.__setattr__(self, "entries", entries)
        object.__setattr__(self, "bound", bound)
        object.__setattr__(self, "hyps", hyps)
        object.__setattr__(self, "bound_ids", ids)

    @classmethod
    def of(cls, *entries: Vars | Hyp) -> "Context":
        return cls().extend(*entries)

    def extend(self, *entries: Vars | Hyp) -> "Context":
        ctx = self
        for entry in entries:
            ctx = Context(ctx, entry)
        return ctx

    def prefix(self, size: int) -> "Context":
        if not 0 <= size <= len(self):
            raise IndexError("Invalid context prefix length")
        ctx = self
        while len(ctx) > size:
            assert ctx.parent is not None
            ctx = ctx.parent
        return ctx

    def __add__(self, entries: tuple[Vars | Hyp, ...]) -> "Context":
        return self.extend(*entries)

    def __len__(self):
        return len(self.entries)

    def __iter__(self):
        return iter(self.entries)

    def __getitem__(self, index: int):
        return self.entries[index]

    def __repr__(self):
        return repr(self.entries)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Context) and _same_context(self, other)


EMPTY = Context()


def _require_context(ctx: Context) -> None:
    if not isinstance(ctx, Context):
        raise TypeError("Expected a checked Context")


def _same_context(left: Context, right: Context) -> bool:
    _require_context(left)
    _require_context(right)
    if left is right:
        return True
    if len(left) != len(right):
        return False
    for a, b in zip(left, right):
        if isinstance(a, Vars) and isinstance(b, Vars):
            if len(a.vs) != len(b.vs) or not all(x.eq(y) for x, y in zip(a.vs, b.vs)):
                return False
        elif not (isinstance(a, Hyp) and isinstance(b, Hyp) and a.thm.eq(b.thm)):
            return False
    return True


def _check_extension(source: Context, target: Context, term: smt.ExprRef) -> None:
    _require_context(target)
    if len(source) > len(target) or not _same_context(
        source, target.prefix(len(source))
    ):
        raise ValueError("Weakening requires an identical context prefix")
    for entry in target.entries[len(source) :]:
        if isinstance(entry, Vars) and not _absent(entry.vs, term):
            raise ValueError("Weakening would capture a free constant")


def _wrap(entry: Vars | Hyp, thm: smt.BoolRef) -> smt.BoolRef:
    return (
        smt.RawForAll(entry.vs, thm)
        if isinstance(entry, Vars)
        else smt.Implies(entry.thm, thm)
    )


@dataclass(frozen=True, eq=False)
class ScopedExpr:
    """A term in an explicit context; a Boolean term is not a proof."""

    ctx: Context
    raw: smt.ExprRef

    def __post_init__(self):
        _require_context(self.ctx)
        if not isinstance(self.raw, smt.ExprRef):
            raise TypeError("Expected a Z3 expression")

    def __repr__(self):
        return f"{self.ctx} |- {self.raw} : {self.raw.sort()}"

    def __bool__(self):
        raise TypeError("Scoped expressions are not Python booleans")

    def weaken(self, ctx: Context) -> "ScopedExpr":
        _check_extension(self.ctx, ctx, self.raw)
        return self if _same_context(self.ctx, ctx) else ScopedExpr(ctx, self.raw)

    def assume(self) -> Context:
        """Extend this term's context with it as a Boolean hypothesis."""
        if not isinstance(self.raw, smt.BoolRef):
            raise TypeError("Only a Boolean expression can be assumed")
        return self.ctx + (Hyp(self.raw),)

    def close(self) -> "ScopedExpr":
        """Close a Boolean proposition using one ForAll/Implies layer."""
        if not isinstance(self.raw, smt.BoolRef) or not self.ctx:
            raise ValueError("close requires a Boolean expression and a context")
        return ScopedExpr(
            self.ctx.prefix(len(self.ctx) - 1), _wrap(self.ctx[-1], self.raw)
        )

    def lambda_(self) -> "ScopedExpr":
        """Abstract the final variable block into a function, preserving its arity."""
        if not self.ctx or not isinstance(self.ctx[-1], Vars):
            raise ValueError("lambda_ requires a final Vars block, not a hypothesis")
        return ScopedExpr(
            self.ctx.prefix(len(self.ctx) - 1), smt.Lambda(self.ctx[-1].vs, self.raw)
        )

    def __add__(self, other) -> "ScopedExpr":
        return lift(op.add, self, other)

    def __radd__(self, other) -> "ScopedExpr":
        return lift(op.add, other, self)

    def __sub__(self, other) -> "ScopedExpr":
        return lift(op.sub, self, other)

    def __mul__(self, other) -> "ScopedExpr":
        return lift(op.mul, self, other)

    def __rmul__(self, other) -> "ScopedExpr":
        return lift(op.mul, other, self)

    def __gt__(self, other) -> "ScopedExpr":
        return lift(op.gt, self, other)

    def __lt__(self, other) -> "ScopedExpr":
        return lift(op.lt, self, other)

    # Like Z3 equality, this constructs a proposition rather than a Python bool.
    def __eq__(self, other) -> "ScopedExpr":  # type: ignore[ty:incompatible-method-override]
        return lift(op.eq, self, other)

    def __getitem__(self, index) -> "ScopedExpr":
        indices = index if isinstance(index, tuple) else (index,)
        return lift(smt.Select, self, *indices)


def variables(
    names: str, sort: smt.SortRef, ctx: Context = EMPTY
) -> tuple[ScopedExpr, ...]:
    """Introduce a named simultaneous variable block without a freshness registry."""
    vs = tuple(smt.Consts(names, sort))
    ctx = ctx + (Vars(vs),)
    return tuple(ScopedExpr(ctx, v) for v in vs)


def lift(fn: Callable, *args) -> ScopedExpr:
    """Apply a Z3 constructor/function, reconciling only prefix-compatible contexts.

    Raw Z3 arguments are rigid empty-context expressions. Python literals are
    passed through for Z3's ordinary sort-directed coercion. No implicit unwrap.
    """
    args = tuple(
        ScopedExpr(EMPTY, a) if isinstance(a, smt.ExprRef) else a for a in args
    )
    ctx = max(
        (a.ctx for a in args if isinstance(a, ScopedExpr)), key=len, default=EMPTY
    )
    raw = [a.weaken(ctx).raw if isinstance(a, ScopedExpr) else a for a in args]
    return ScopedExpr(ctx, fn(*raw))


def internalize(ctx: Context, thm: smt.BoolRef) -> smt.BoolRef:
    """Fold a telescope into raw ForAll blocks and curried implications."""
    for entry in reversed(ctx):
        thm = _wrap(entry, thm)
    return thm


def _close_vars(
    ctx: Context,
    thm: smt.BoolRef,
    build: Callable[[dict[smt.ExprRef, smt.ExprRef]], kernel.Proof],
) -> kernel.Proof:
    """Compile an all-variable telescope back to the old kernel.

    Herbrand constants are confined to this adapter; no FreshVar registration.
    A native scoped kernel could replace this compatibility step. Normally
    no solver is needed; differing retained binder names may require repair.
    """
    goal = internalize(ctx, thm)
    bindings = {}
    closing = []
    for entry in ctx:
        assert isinstance(entry, Vars)
        assert isinstance(goal, smt.QuantifierRef) and goal.is_forall()
        vs, rule = kernel.herb(goal)
        bindings.update(zip(entry.vs, vs))
        closing.append(rule)
        goal = rule.thm.arg(0)
    result = build(bindings)
    if not result.thm.eq(goal):
        # The certificate may retain different names after fix/close roundtrips.
        result = kernel.prove(goal, by=[result])
    for rule in reversed(closing):
        result = kernel.modus(rule, result)
    return result


@dataclass(frozen=True, eq=False)
class ScopedProof:
    """A scoped judgment with a kernel certificate for its internalization."""

    ctx: Context
    thm: smt.BoolRef
    closed: kernel.Proof

    def __post_init__(self):
        _require_context(self.ctx)
        if not isinstance(self.thm, smt.BoolRef) or not isinstance(
            self.closed, kernel.Proof
        ):
            raise TypeError("Expected a Boolean conclusion and a kernel Proof")
        if self.closed.fvs or not utils.alpha_eq(self.to_expr(), self.closed.thm):
            raise ValueError("Certificate does not prove the internalized judgment")

    def __repr__(self):
        return f"{self.ctx} |- {self.thm}"

    @classmethod
    def from_proof(cls, pf: kernel.Proof, ctx: Context = EMPTY) -> "ScopedProof":
        """Import a closed theorem, weakening before any local instantiation."""
        return cls(EMPTY, pf.thm, pf).weaken(ctx)

    @property
    def expr(self) -> ScopedExpr:
        """The proposition proved by this judgment, retaining its context."""
        return ScopedExpr(self.ctx, self.thm)

    def to_expr(self) -> smt.BoolRef:
        """Internalize this judgment, preserving telescope order and grouping."""
        return internalize(self.ctx, self.thm)

    def fix(self, vs: tuple[smt.ExprRef, ...]) -> "ScopedProof":
        """Expose one forall block using explicitly named local constants."""
        q = self.thm
        if not isinstance(q, smt.QuantifierRef) or not q.is_forall():
            raise ValueError("fix expects a universal conclusion")
        if len(vs) != q.num_vars() or any(
            v.sort() != q.var_sort(i) for i, v in enumerate(vs)
        ):
            raise ValueError("Binder count or sorts do not match")
        ctx = self.ctx.extend(Vars(vs))
        if not _absent(vs, self.to_expr()):
            raise ValueError("Opening binders would capture a free constant")
        body = smt.substitute_vars(q.body(), *reversed(vs))
        return ScopedProof(ctx, body, self.closed)

    def intro(self) -> "ScopedProof":
        """Expose one implication premise in the context."""
        if not smt.is_implies(self.thm):
            raise ValueError("intro expects an implication")
        return ScopedProof(
            self.ctx + (Hyp(self.thm.arg(0)),), self.thm.arg(1), self.closed
        )

    def close(self) -> "ScopedProof":
        """Move the final context entry back onto the conclusion."""
        if not self.ctx:
            raise ValueError("No context entry to close")
        return ScopedProof(
            self.ctx.prefix(len(self.ctx) - 1),
            _wrap(self.ctx[-1], self.thm),
            self.closed,
        )

    def weaken(self, ctx: Context) -> "ScopedProof":
        """Transport along the projection from an extended context."""
        if _same_context(self.ctx, ctx):
            return self
        _check_extension(self.ctx, ctx, self.thm)
        return Subst.projection(ctx, self.ctx).apply(self)

    def subst(
        self, index: int, terms: tuple[smt.ExprRef | ScopedExpr, ...]
    ) -> "ScopedProof":
        """Instantiate a whole block with prefix terms, then transport the forest."""
        entry = self.ctx[index]
        if not isinstance(entry, Vars):
            raise ValueError("Substitution expects a Vars entry")
        if index < 0:
            index += len(self.ctx)
        prefix = self.ctx.prefix(index)
        terms = tuple(
            t.weaken(prefix).raw if isinstance(t, ScopedExpr) else t for t in terms
        )
        if len(terms) != len(entry.vs) or any(
            t.sort() != v.sort() for t, v in zip(terms, entry.vs)
        ):
            raise ValueError("Substitution count or sorts do not match")
        unavailable = self.ctx.bound[len(prefix.bound) :]
        if any(not _absent(unavailable, t) for t in terms):
            raise ValueError(
                "Substitution terms depend on this block or later variables"
            )
        pairs = list(zip(entry.vs, terms))
        ctx = prefix
        for e in self.ctx.entries[index + 1 :]:
            ctx = ctx.extend(
                Hyp(smt.substitute(e.thm, *pairs)) if isinstance(e, Hyp) else e
            )
        forest, pairs = [], []
        for i, e in enumerate(self.ctx):
            if isinstance(e, Vars):
                values = tuple(
                    ScopedExpr(ctx, t) for t in (terms if i == index else e.vs)
                )
                forest.append(values)
                pairs.extend(zip(e.vs, (t.raw for t in values)))
            else:
                forest.append(prove(smt.substitute(e.thm, *pairs), ctx=ctx))
        return Subst(ctx, self.ctx, tuple(forest)).apply(self)

    def __call__(
        self, *args: "smt.ExprRef | ScopedExpr | ScopedProof | kernel.Proof"
    ) -> "ScopedProof":
        """Read arguments as a telescope forest, then apply one checked Subst."""
        if not args:
            return self
        ctx = max(
            [self.ctx]
            + [a.ctx for a in args if isinstance(a, (ScopedExpr, ScopedProof))],
            key=len,
        )
        forest = list(Subst.projection(ctx, self.ctx).values)
        opened, pos = self, 0
        while pos < len(args):
            q = opened.thm
            if isinstance(q, smt.QuantifierRef) and q.is_forall():
                count = q.num_vars()
                supplied = args[pos : pos + count]
                if len(supplied) != count:
                    raise ValueError("Supply a term for each variable in the block")
                terms = []
                for term in supplied:
                    if isinstance(term, smt.ExprRef):
                        term = ScopedExpr(ctx, term)
                    if not isinstance(term, ScopedExpr):
                        raise TypeError("Expected a term of the quantified sort")
                    terms.append(term)
                vs, _ = kernel.open_binder(q)
                opened = opened.fix(tuple(vs))
                forest.append(tuple(terms))
                pos += count
            elif smt.is_implies(q):
                evidence = args[pos]
                if isinstance(evidence, kernel.Proof):
                    evidence = ScopedProof.from_proof(evidence, ctx)
                if not isinstance(evidence, ScopedProof):
                    raise TypeError("Implication arguments must be proofs")
                opened = opened.intro()
                forest.append(evidence)
                pos += 1
            else:
                raise ValueError("Application expects a forall or implication")
        return Subst(ctx, opened.ctx, tuple(forest)).apply(opened)


@dataclass(frozen=True, eq=False)
class Subst:
    """src |- values : dst: scoped terms for Vars, evidence for instantiated Hyps."""

    src: Context
    dst: Context
    values: tuple[tuple[ScopedExpr, ...] | ScopedProof, ...]
    pairs: tuple[tuple[smt.ExprRef, smt.ExprRef], ...] = field(init=False, repr=False)

    def __post_init__(self):
        _require_context(self.src)
        _require_context(self.dst)
        if not isinstance(self.values, tuple) or len(self.values) != len(self.dst):
            raise ValueError("Forest must have one component per destination entry")
        if not _absent(self.src.bound, internalize(self.dst, smt.BoolVal(True))):
            raise ValueError(
                "Substitution would capture a rigid constant in the context"
            )
        values, pairs = [], []
        for entry, value in zip(self.dst, self.values):
            if isinstance(entry, Vars):
                if not isinstance(value, tuple) or len(value) != len(entry.vs):
                    raise ValueError("Supply a term for each variable in the block")
                if not all(isinstance(t, ScopedExpr) for t in value):
                    raise TypeError("Vars slots require scoped terms")
                terms = tuple(t.weaken(self.src) for t in value)
                if any(t.raw.sort() != v.sort() for t, v in zip(terms, entry.vs)):
                    raise TypeError("Expected a term of the quantified sort")
                pairs.extend(zip(entry.vs, (t.raw for t in terms)))
                values.append(terms)
            else:
                if not isinstance(value, ScopedProof):
                    raise TypeError("Hyp slots require proofs, not Boolean expressions")
                evidence = value.weaken(self.src)
                expected = smt.substitute(entry.thm, *pairs)
                if not utils.alpha_eq(expected, evidence.thm):
                    raise ValueError(
                        "Proof does not match the instantiated hypothesis premise"
                    )
                values.append(evidence)
        object.__setattr__(self, "values", tuple(values))
        object.__setattr__(self, "pairs", tuple(pairs))

    @classmethod
    def projection(cls, src: Context, dst: Context) -> "Subst":
        """The weakening projection from an extended context to its prefix."""
        _check_extension(dst, src, smt.BoolVal(True))
        forest = tuple(
            tuple(ScopedExpr(src, v) for v in entry.vs)
            if isinstance(entry, Vars)
            else prove(entry.thm, ctx=src)
            for entry in dst
        )
        return cls(src, dst, forest)

    @classmethod
    def identity(cls, ctx: Context) -> "Subst":
        return cls.projection(ctx, ctx)

    @overload
    def apply(self, value: ScopedExpr) -> ScopedExpr: ...

    @overload
    def apply(self, value: ScopedProof) -> ScopedProof: ...

    def apply(self, value: ScopedExpr | ScopedProof) -> ScopedExpr | ScopedProof:
        """Transport a term or proof from dst to src; never capture rigid globals."""
        value = value.weaken(self.dst)
        raw = value.raw if isinstance(value, ScopedExpr) else value.thm
        abstract = smt.Lambda(self.dst.bound, raw) if self.dst.bound else raw
        if not _absent(self.src.bound, abstract):
            raise ValueError("Substitution would capture a rigid constant")
        result = smt.substitute(raw, *self.pairs)
        if isinstance(value, ScopedExpr):
            return ScopedExpr(self.src, result)
        if all(isinstance(e, Vars) for e in self.src):

            def build(bindings):
                pf = value.closed
                variables = [bindings[v] for v in self.src.bound]
                for entry, component in zip(self.dst, self.values):
                    if isinstance(entry, Vars):
                        assert isinstance(component, tuple)
                        terms = [
                            smt.substitute(t.raw, *bindings.items()) for t in component
                        ]
                        pf = kernel.instan(terms, pf)
                    else:
                        assert isinstance(component, ScopedProof)
                        evidence = component.closed(*variables)
                        if not pf.thm.arg(0).eq(evidence.thm):
                            evidence = kernel.prove(pf.thm.arg(0), by=[evidence])
                        pf = kernel.modus(pf, evidence)
                return pf

            certificate = _close_vars(self.src, result, build)
        else:
            evidence = [v.closed for v in self.values if isinstance(v, ScopedProof)]
            certificate = kernel.prove(
                internalize(self.src, result), by=[value.closed, *evidence]
            )
        return ScopedProof(self.src, result, certificate)

    def then(self, after: "Subst") -> "Subst":
        """Compose src -> dst -> after.dst by substituting the entire forest."""
        if not _same_context(self.dst, after.src):
            raise ValueError("Substitution composition has mismatched contexts")
        forest = tuple(
            tuple(self.apply(t) for t in value)
            if isinstance(value, tuple)
            else self.apply(value)
            for value in after.values
        )
        return Subst(self.src, after.dst, forest)


def prove(
    thm: smt.BoolRef | ScopedExpr,
    *,
    ctx: Context | None = None,
    by: Sequence[ScopedProof | kernel.Proof] = (),
    **kwargs,
) -> ScopedProof:
    """Prove a contextual goal, using a scoped proposition's context by default."""
    if isinstance(thm, ScopedExpr):
        ctx = thm.ctx if ctx is None else ctx
        raw = thm.weaken(ctx).raw
    else:
        raw = thm
    ctx = EMPTY if ctx is None else ctx
    if not isinstance(raw, smt.BoolRef):
        raise TypeError("prove requires a Boolean proposition, not an arbitrary term")
    _require_context(ctx)
    premises = [
        p if isinstance(p, ScopedProof) else ScopedProof.from_proof(p) for p in by
    ]
    aligned = [p.weaken(ctx).closed for p in premises]
    return ScopedProof(
        ctx, raw, kernel.prove(internalize(ctx, raw), by=aligned, **kwargs)
    )
