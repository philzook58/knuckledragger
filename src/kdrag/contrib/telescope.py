"""Experimental ordered contexts, backed by existing closed kernel proofs.

No FreshVar registry or new trusted rules. All-variable application/weakening
compile through the old kernel's Herbrand and instantiation rules. Other
structural transformations currently use Z3; this is an API prototype.
"""

from dataclasses import dataclass
from typing import Callable, Sequence

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
    def from_proof(cls, pf: kernel.Proof, ctx: Context = ()) -> "ScopedProof":
        """Import a closed theorem, weakening before any local instantiation."""
        return cls((), pf.thm, pf).weaken(ctx)

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
        if all(isinstance(e, Vars) for e in ctx):

            def build(bindings):
                return self.closed(
                    *(
                        bindings[v]
                        for e in self.ctx
                        if isinstance(e, Vars)
                        for v in e.vs
                    )
                )

            return ScopedProof(ctx, self.thm, _close_vars(ctx, self.thm, build))
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

    def __call__(
        self, *args: "smt.ExprRef | ScopedProof | kernel.Proof"
    ) -> "ScopedProof":
        """Apply forall terms and premise proofs in the current context.

        Import closed lemmas into the context *before* applying local variables.
        All-variable contexts replay existing kernel rules without search;
        contexts with hypotheses currently certify the result with Z3.
        """
        if not args:
            return self
        thm, pos = self.thm, 0
        premises = [self]
        applied = []
        while pos < len(args):
            if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
                count = thm.num_vars()
                supplied = args[pos : pos + count]
                if len(supplied) != count:
                    raise ValueError("Supply a term for each variable in the block")
                terms = []
                for i, term in enumerate(supplied):
                    if not isinstance(term, smt.ExprRef) or term.sort() != thm.var_sort(
                        i
                    ):
                        raise TypeError("Expected a term of the quantified sort")
                    terms.append(term)
                applied.extend(terms)
                thm = smt.substitute_vars(thm.body(), *reversed(terms))
                pos += count
            elif smt.is_implies(thm):
                evidence = args[pos]
                if isinstance(evidence, kernel.Proof):
                    evidence = ScopedProof.from_proof(evidence, self.ctx)
                if not isinstance(evidence, ScopedProof):
                    raise TypeError("Implication arguments must be proofs")
                evidence = evidence.weaken(self.ctx)
                if not utils.alpha_eq(thm.arg(0), evidence.thm):
                    raise ValueError("Proof does not match the implication premise")
                premises.append(evidence)
                applied.append(evidence)
                thm = thm.arg(1)
                pos += 1
            else:
                raise ValueError("Application expects a forall or implication")
        if all(isinstance(e, Vars) for e in self.ctx):

            def build(bindings):
                variables = [
                    bindings[v] for e in self.ctx if isinstance(e, Vars) for v in e.vs
                ]
                args = [
                    a.closed(*variables)
                    if isinstance(a, ScopedProof)
                    else smt.substitute(a, *bindings.items())
                    for a in applied
                ]
                return self.closed(*variables)(*args)

            return ScopedProof(self.ctx, thm, _close_vars(self.ctx, thm, build))
        return prove(thm, ctx=self.ctx, by=premises)

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
