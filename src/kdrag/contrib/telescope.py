"""Experimental ordered contexts, backed by existing closed kernel proofs.

No FreshVar registry or new trusted rules. Structural transformations that
change the internalized formula currently use Z3; this is an API prototype.
"""

from dataclasses import dataclass
from typing import Sequence

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


Context = tuple[Vars | Hyp, ...]


def _absent(vs: Sequence[smt.ExprRef], thm: smt.ExprRef) -> bool:
    return not vs or utils.free_in(list(vs), thm)


def _validate(ctx: Context) -> None:
    if not isinstance(ctx, tuple):
        raise TypeError("Context must be a tuple")
    variables = []
    for entry in ctx:
        if isinstance(entry, Vars):
            if not isinstance(entry.vs, tuple) or not entry.vs:
                raise ValueError("Vars requires a nonempty tuple")
            if not all(smt.is_const(v) and smt.is_uninterp(v) for v in entry.vs):
                raise ValueError("Binders must be uninterpreted constants")
            variables.extend(entry.vs)
        elif not isinstance(entry, Hyp) or not isinstance(entry.thm, smt.BoolRef):
            raise TypeError("Context entries must be Vars or Boolean Hyp entries")
    if len({v.get_id() for v in variables}) != len(variables):
        raise ValueError("Context binders must be distinct")
    for entry in ctx:
        if isinstance(entry, Vars):
            variables = variables[len(entry.vs) :]
        elif not _absent(variables, entry.thm):
            raise ValueError("Hypothesis refers to a later context variable")


def _same_context(left: Context, right: Context) -> bool:
    if len(left) != len(right):
        return False
    for a, b in zip(left, right):
        if isinstance(a, Vars) and isinstance(b, Vars):
            if len(a.vs) != len(b.vs) or not all(x.eq(y) for x, y in zip(a.vs, b.vs)):
                return False
        elif not (isinstance(a, Hyp) and isinstance(b, Hyp) and a.thm.eq(b.thm)):
            return False
    return True


def internalize(ctx: Context, thm: smt.BoolRef) -> smt.BoolRef:
    """Fold a telescope into raw ForAll blocks and curried implications."""
    for entry in reversed(ctx):
        thm = (
            smt.RawForAll(entry.vs, thm)
            if isinstance(entry, Vars)
            else smt.Implies(entry.thm, thm)
        )
    return thm


@dataclass(frozen=True, eq=False)
class ScopedProof:
    """A scoped judgment with a kernel certificate for its internalization."""

    ctx: Context
    thm: smt.BoolRef
    closed: kernel.Proof

    def __post_init__(self):
        _validate(self.ctx)
        if not isinstance(self.thm, smt.BoolRef) or not isinstance(
            self.closed, kernel.Proof
        ):
            raise TypeError("Expected a Boolean conclusion and a kernel Proof")
        if self.closed.fvs or not utils.alpha_eq(self.to_expr(), self.closed.thm):
            raise ValueError("Certificate does not prove the internalized judgment")

    def __repr__(self):
        return f"{self.ctx} |- {self.thm}"

    @classmethod
    def from_proof(cls, pf: kernel.Proof) -> "ScopedProof":
        """Import an existing theorem with an empty context."""
        return cls((), pf.thm, pf)

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
        _validate(self.ctx + (Vars(vs),))
        if not _absent(vs, self.to_expr()):
            raise ValueError("Opening binders would capture a free constant")
        body = smt.substitute_vars(q.body(), *reversed(vs))
        return ScopedProof(self.ctx + (Vars(vs),), body, self.closed)

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
            self.ctx[:-1], internalize(self.ctx[-1:], self.thm), self.closed
        )

    def weaken(self, ctx: Context) -> "ScopedProof":
        """Extend a matching prefix without capturing existing free constants."""
        _validate(ctx)
        if not _same_context(self.ctx, ctx[: len(self.ctx)]):
            raise ValueError("Weakening requires an identical context prefix")
        if _same_context(self.ctx, ctx):
            return self
        for entry in ctx[len(self.ctx) :]:
            if isinstance(entry, Vars) and not _absent(entry.vs, self.thm):
                raise ValueError("Weakening would capture a free constant")
        return self._derive(ctx, self.thm)

    def subst(self, index: int, terms: tuple[smt.ExprRef, ...]) -> "ScopedProof":
        """Instantiate an entire variable block using terms available in its prefix."""
        entry = self.ctx[index]
        if not isinstance(entry, Vars):
            raise ValueError("Substitution expects a Vars entry")
        if index < 0:
            index += len(self.ctx)
        if len(terms) != len(entry.vs) or any(
            t.sort() != v.sort() for t, v in zip(terms, entry.vs)
        ):
            raise ValueError("Substitution count or sorts do not match")
        unavailable = [v for e in self.ctx[index:] if isinstance(e, Vars) for v in e.vs]
        if any(not _absent(unavailable, t) for t in terms):
            raise ValueError(
                "Substitution terms depend on this block or later variables"
            )
        pairs = list(zip(entry.vs, terms))
        suffix = tuple(
            Hyp(smt.substitute(e.thm, *pairs)) if isinstance(e, Hyp) else e
            for e in self.ctx[index + 1 :]
        )
        return self._derive(self.ctx[:index] + suffix, smt.substitute(self.thm, *pairs))

    def _derive(self, ctx: Context, thm: smt.BoolRef) -> "ScopedProof":
        _validate(ctx)
        return ScopedProof(
            ctx, thm, kernel.prove(internalize(ctx, thm), by=[self.closed])
        )


def prove(
    thm: smt.BoolRef,
    *,
    ctx: Context = (),
    by: Sequence[ScopedProof | kernel.Proof] = (),
    **kwargs,
) -> ScopedProof:
    """Prove a contextual goal, reconciling only identical/prefix contexts."""
    _validate(ctx)
    premises = [
        p if isinstance(p, ScopedProof) else ScopedProof.from_proof(p) for p in by
    ]
    aligned = [p.weaken(ctx).closed for p in premises]
    return ScopedProof(
        ctx, thm, kernel.prove(internalize(ctx, thm), by=aligned, **kwargs)
    )
