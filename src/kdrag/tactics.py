"""
Tactics are helpers that organize calls to the kernel. The code of these helpers don't have to be trusted.
"""

import kdrag as kd
import kdrag.smt as smt
import kdrag.config
import kdrag.rewrite
from enum import IntEnum
import operator as op
from typing import NamedTuple, Optional, Sequence, Callable
import pprint
import time
from dataclasses import dataclass
import kdrag.parsers.microlean as microlean
import kdrag.reflect as reflect


def FreshVar(name: str, sort: smt.SortRef, assume=None) -> smt.ExprRef:
    """
    Create a schema variable with the given name and sort.
    """
    v = kd.kernel.FreshVar(name, sort)
    if assume is not None:
        v.assume = assume(v)  # type: ignore
    return v


def FreshVars(names: str, sort: smt.SortRef) -> list[smt.ExprRef]:
    """
    Create a list of schema variables with the given names and sort.
    """
    return [kd.kernel.FreshVar(name, sort) for name in names.split()]


def ForAllI(vs: list[smt.ExprRef], pf: kd.kernel.Proof) -> kd.kernel.Proof:
    """
    All vs must be FreshVars
    Combinator name tries to make it clear that this is a
    smt.ForAll that works on Proofs instead of BoolRefs.
    """
    return kd.kernel.generalize(vs, pf)


def open_binder(pf: kd.kernel.Proof) -> tuple[list[smt.ExprRef], kd.kernel.Proof]:
    """
    Open a proof with schematic variables so that it can be reconstructed.

    >>> x,y,z = smt.Reals("x y z")
    >>> pf = kd.prove(smt.ForAll([x,y], x + y + 1 > x + y))
    >>> open_binder(pf)
    ([x!..., y!...], |= x!... + y!... + 1 > x!... + y!...)
    """
    thm = pf.thm
    assert isinstance(pf, kd.Proof) and isinstance(thm, smt.QuantifierRef)
    vs = [
        kd.kernel.FreshVar(thm.var_name(n), thm.var_sort(n))
        for n in range(thm.num_vars())
    ]
    return vs, pf(*vs)


def forallI(
    e: smt.QuantifierRef, cb: Callable[[smt.BoolRef, smt.ExprRef], kd.kernel.Proof]
) -> kd.kernel.Proof:
    """
    Open a forall quantifier but giving a new goal and fresh variables to a callback function.

    >>> x = smt.Int("x")
    >>> forallI(smt.ForAll([x], x > x - 1), lambda goal, x1: kd.prove(goal))
    |= ForAll(x, x > x - 1)
    """
    assert isinstance(e, smt.QuantifierRef) and e.is_forall(), (
        "forallI only works on forall quantifiers"
    )
    vs, ab = kd.kernel.herb(e)
    a = cb(ab.thm.arg(0), *vs)
    return kd.kernel.modus(ab, a)


def skolem(pf: kd.kernel.Proof) -> tuple[list[smt.ExprRef], kd.kernel.Proof]:
    """
    Skolemize an existential quantifier.

    >>> x = smt.Int("x")
    >>> pf = kd.prove(smt.Exists([x], x > 0))
    >>> skolem(pf)
    ([x!...], |= x!... > 0)
    """
    thm = pf.thm
    assert isinstance(thm, smt.QuantifierRef)
    skolems, pfab = kd.kernel.obtain(thm)
    return skolems, kd.kernel.modus(pfab, pf)


class Calc:
    """
    Calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    """

    class _Mode(IntEnum):
        EQ = 0
        LE = 1
        LT = 2
        GT = 3
        GE = 4

        def __str__(self):
            names = ["==", "<=", "<", ">", ">="]
            return names[self]

        @property
        def op(self):
            ops = [op.eq, op.le, op.lt, op.gt, op.ge]
            return ops[self]

        def trans(self, y):
            """Allowed transitions"""
            if self == y or self == self.EQ:
                return True
            else:
                if self == self.LE and y == self.LT or self == self.GE and y == self.GT:
                    return True
                else:
                    return False

    def __init__(self, vars: list[smt.ExprRef], lhs: smt.ExprRef, assume=[]):
        self.start_time = time.perf_counter()
        self.vars = vars
        self.lhs = lhs
        self.iterm = lhs  # intermediate term
        self.assume = assume
        self.lemma = kd.kernel.prove(self._forall(smt.Eq(lhs, lhs)))
        self.mode = self._Mode.EQ

    def _forall(
        self, body: smt.BoolRef | smt.QuantifierRef
    ) -> smt.BoolRef | smt.QuantifierRef:
        if len(self.assume) == 1:
            body = smt.Implies(self.assume[0], body)
        elif len(self.assume) > 1:
            body = smt.Implies(smt.And(self.assume), body)
        if len(self.vars) == 0:
            return body
        else:
            return smt.ForAll(self.vars, body)

    def _lemma(self, rhs, by, **kwargs):
        op = self.mode.op
        l = kd.kernel.prove(self._forall(op(self.iterm, rhs)), by=by, **kwargs)
        self.lemma = kd.prove(
            self._forall(op(self.lhs, rhs)), by=[l, self.lemma], **kwargs
        )
        self.iterm = rhs

    def eq(self, rhs, by=[], **kwargs):
        self._lemma(rhs, by, **kwargs)
        return self

    def _set_mode(self, newmode):
        if not self.mode.trans(newmode):
            raise kd.kernel.LemmaError(
                "Cannot change from", self.mode, "to", newmode, "in Calc"
            )
        self.mode = newmode

    def le(self, rhs, by=[]):
        self._set_mode(Calc._Mode.LE)
        self._lemma(rhs, by)
        return self

    def lt(self, rhs, by=[]):
        self._set_mode(Calc._Mode.LT)
        self._lemma(rhs, by)
        return self

    def ge(self, rhs, by=[]):
        self._set_mode(Calc._Mode.GE)
        self._lemma(rhs, by)
        return self

    def gt(self, rhs, by=[]):
        self._set_mode(Calc._Mode.GT)
        self._lemma(rhs, by)
        return self

    def __repr__(self):
        return "... " + str(self.mode) + " " + repr(self.iterm)

    def qed(self, **kwargs):
        kdrag.config.perf_event(
            "Calc", self.lemma, time.perf_counter() - self.start_time
        )
        return self.lemma


def simp_tac(e: smt.ExprRef) -> kd.kernel.Proof:
    """
    Simplify an expression using simp and return the resulting equality as a proof.

    >>> import kdrag.theories.nat as nat
    >>> simp_tac(nat.Z + nat.S(nat.Z))
    |= add(Z, S(Z)) == S(Z)
    """
    trace = []
    e1 = kd.simp(e, trace=trace)
    return kd.kernel.prove(smt.Eq(e, e1), by=trace)


simps = {}


def auto(shows=None, **kwargs) -> kd.kernel.Proof:
    # enables shows parameter. Should I just put this in prove? Makes it a bit weird
    assert shows is not None
    return kd.prove(shows, **kwargs)


def prove(
    thm: smt.BoolRef,
    fixes: list[smt.ExprRef] = [],
    assumes: list[smt.BoolRef] = [],
    by: Optional[kd.kernel.Proof | Sequence[kd.kernel.Proof]] = None,
    admit=False,
    timeout=1000,
    dump=False,
    solver=None,
    # defns=True,
    # induct=False,
    # simps=simps,
    # intros / fix / herb = False
    unfold: Optional[int | list[smt.FuncDeclRef]] = None,
) -> kd.kernel.Proof:
    """Prove a theorem using a list of previously proved lemmas.

    In essence `prove(Implies(by, thm))`.

    This wraps the kernel version in order to provide better counterexamples.

    :param thm: The theorem to prove.
    Args:
        thm (smt.BoolRef): The theorem to prove.
        by (list[Proof]): A list of previously proved lemmas.
        admit     (bool): If True, admit the theorem without proof.

    Returns:
        Proof: A proof object of thm

    >>> prove(smt.BoolVal(True))
    |= True

    >>> prove(smt.RealVal(1) >= smt.RealVal(0))
    |= 1 >= 0

    >>> x = smt.Int("x")
    >>> succ = kd.define("succ", [x], x + 1)
    >>> prove(succ(x) == x + 1, unfold=1)
    |= succ(x) == x + 1
    >>> succ2 = kd.define("succ2", [x], succ(succ(x)))
    >>> prove(succ2(x) == x + 2, unfold=2)
    |= succ2(x) == x + 2
    >>> prove(succ(x) == x + 1, unfold=[succ])
    |= succ(x) == x + 1
    """
    start_time = time.perf_counter()

    if assumes:
        thm = smt.Implies(smt.And(assumes), thm)

    if by is None:
        by = []
    elif isinstance(by, kd.Proof):
        by = [by]
    elif not isinstance(by, list):
        by = list(by)

    if unfold is None:
        pass
    elif isinstance(unfold, int):
        trace = []
        thm1 = thm
        for i in range(unfold):
            thm1 = kd.rewrite.unfold(thm1, trace=trace)
        # It is arguable if we're better off dumping trace into by or hiding trace
        if not thm.eq(thm1):
            by.extend(trace)
    elif isinstance(unfold, list):
        trace = []
        thm1 = kd.rewrite.unfold(thm, decls=unfold, trace=trace)
        if not thm.eq(thm1):
            by.extend(trace)

    try:
        pf = kd.kernel.prove(
            thm, by, timeout=timeout, dump=dump, solver=solver, admit=admit
        )
        if fixes:
            pf = kd.kernel.generalize(fixes, pf)
        kdrag.config.perf_event("prove", thm, time.perf_counter() - start_time)
        return pf
    except kd.kernel.LemmaError as e:
        if time.perf_counter() - start_time > timeout / 1000:
            raise TimeoutError(
                "Timeout. Maybe you have given `prove` too many or not enough lemmas?"
            )
        elif isinstance(thm, smt.QuantifierRef):
            while isinstance(thm, smt.QuantifierRef) and thm.is_forall():
                _, thm = kd.utils.open_binder_unhygienic(thm)  # type: ignore
            # We anticipate this failing with a better countermodel since we can now see the quantified variables
            pf = kd.kernel.prove(
                thm, by=by, timeout=timeout, dump=dump, solver=solver, admit=admit
            )
            # TODO: Maybe we should herbrandize and just let the quantifier free version work for us.
            raise Exception(
                "Worked with quantifier stripped. Something is going awry", pf
            )
        else:
            raise e
    except Exception as e:
        raise e


def simp(t: smt.ExprRef, by: list[kd.kernel.Proof] = [], **kwargs) -> kd.kernel.Proof:
    rules = [kd.rewrite.rewrite_of_expr(lem.thm) for lem in by]
    t1 = kd.rewrite.rewrite_once(t, rules)
    return prove(smt.Eq(t, t1), by=by, **kwargs)


def subst(
    pf: kd.kernel.Proof, vs: list[smt.ExprRef], subst: list[smt.ExprRef]
) -> kd.kernel.Proof:
    """
    Perform substitution into a forall quantified proof, instantiating into a new context vs

    >>> x,y,z = smt.Reals("x y z")
    >>> p = kd.prove(smt.ForAll([x,z], smt.And(z == z, x == x)))
    >>> subst(p, [y, z], [y + 1, z])
    |= ForAll([y, z], And(z == z, y + 1 == y + 1))
    """
    assert isinstance(pf.thm, smt.QuantifierRef)
    vs1, ab = kd.kernel.herb(
        smt.ForAll(vs, smt.substitute_vars(pf.thm.body(), *reversed(subst)))
    )
    a = kd.kernel.instan([smt.substitute(t, *zip(vs, vs1)) for t in subst], pf)
    return kd.kernel.modus(ab, a)


class Goal(NamedTuple):
    # TODO: also put eigenvariables, unification variables in here
    sig: list[smt.ExprRef]
    ctx: list[smt.BoolRef]
    goal: smt.BoolRef | smt.QuantifierRef

    def __repr__(self):
        if self.is_empty():
            return "Nothing to do!"
        ctxrepr = pprint.pformat(self.ctx)
        goalrepr = repr(self.goal)
        if len(ctxrepr) + len(goalrepr) <= 75:
            goalctx = ctxrepr + " ?|= " + repr(self.goal)
        else:
            goalctx = ctxrepr + "\n?|= " + repr(self.goal)
        if len(self.sig) == 0:
            return goalctx
        else:
            sigrepr = pprint.pformat(self.sig)
            if len(sigrepr) + len(goalctx) >= 80:
                return repr(self.sig) + ";\n" + goalctx
            else:
                return repr(self.sig) + " ; " + goalctx

    # def formula(self) -> smt.BoolRef:
    #   return kd.QForAll(self.sig, *self.ctx, self.goal)

    @classmethod
    def empty(cls) -> "Goal":
        return Goal(
            [],
            [],
            smt.Or(
                smt.BoolVal(True), smt.Bool("KNUCKLEDRAGGER_EMPTYGOAL")
            ),  # trivial _and_ specially marked
        )

    def to_expr(self):
        """
        Convert goal into formula it represents

        >>> x = smt.Int("x")
        >>> Goal(sig=[x], ctx=[x > 0], goal=x > -1).to_expr()
        Implies(x > 0, x > -1)
        >>> Goal(sig=[], ctx=[], goal=x > 0).to_expr()
        x > 0
        >>> Goal(sig=[], ctx=[x > 0], goal=x > -1).to_expr()
        Implies(x > 0, x > -1)
        """
        if self.ctx:
            return kd.QImplies(*self.ctx, self.goal)
        else:
            return self.goal

    def proof(self) -> "ProofState":
        return ProofState(self)

    def is_empty(self) -> bool:
        return self == Goal.empty()


@dataclass
class LemmaCallback:
    cb: Callable[[], None]
    annot: object = None


def Lemma(goal: smt.BoolRef, fixes=None, assumes=None) -> "ProofState":
    return Goal(
        sig=[] if fixes is None else fixes,
        ctx=[] if assumes is None else assumes,
        goal=goal,
    ).proof()


class ProofState:
    """
    A tactic class for interactive proofs.
    `ProofState` stores a mutational partial proof state that can be changed via tactic methods.
    Once proof is completed, an actual `kd.Proof` object is constructed by the `Lemma.qed` method.
    `ProofState` is not part of the trusted code base and bugs in its implementation are not a soundness concern.
    `ProofState` "merely" orchestrates and infers info for calls to the kernel.
    In my experience it is best to run the entire Lemma mutation in a single Jupyter cell while experimenting.

    ProofState can be seen as
    - A Builder or Factory for kd.Proof objects. `l.qed()` is the analog of a `build` function which calls the constructor `kd.prove` under the hood
    - A node of a Zipper-like context for a proof tree. In other words a partially complete proof.

    """

    def __init__(self, goal: Goal, _parent=None):
        self.start_time = time.perf_counter()
        self.lemmas: list[dict[int, kdrag.kernel.Proof]] = [{}]
        self.thm = goal
        self.goals: list[Goal | LemmaCallback] = [goal]
        self.pushed = None
        self._parent = _parent

    def add_lemma(self, lemma: kd.kernel.Proof):
        """
        Record a lemma in the current ProofState state.
        """
        self.lemmas[-1][lemma.thm.get_id()] = lemma

    def get_lemma(self, thm: smt.BoolRef) -> kd.kernel.Proof:
        l = self.lemmas[-1].get(thm.get_id())
        if l is None:
            return kdrag.kernel.prove(thm, by=list(self.lemmas[-1].values()))
        else:
            return l

    def push_lemmas(self):
        self.lemmas.append({})

    def pop_lemmas(self):
        self.lemmas.pop()

    def copy(self):
        """
        ProofState methods mutates the proof state. This can make you a copy.
        Does not copy the pushed ProofState stack.

        >>> p,q = smt.Bools("p q")
        >>> l = Lemma(smt.Implies(p,q))
        >>> l1 = l.copy()
        >>> l.intros()
        [p] ?|= q
        >>> l1
        [] ?|= Implies(p, q)
        """
        lemma_cpy = ProofState(self.thm, _parent=self._parent)
        lemma_cpy.goals = self.goals.copy()
        lemma_cpy.lemmas = self.lemmas.copy()
        lemma_cpy.pushed = None
        return lemma_cpy

    def push(self):
        """
        Push a copy of the current ProofState state onto a stack.
        This why you can try things out, and if they fail

        >>> p,q = smt.Bools("p q")
        >>> l = Lemma(smt.Implies(p,q))
        >>> l.push()
        [] ?|= Implies(p, q)
        >>> l.intros()
        [p] ?|= q
        >>> l.pop()
        [] ?|= Implies(p, q)
        """
        cpy = self.copy()
        cpy.pushed = self.pushed
        self.pushed = cpy
        return self.top_goal()

    def pop(self):
        """
        Pop state off the ProofState stack.
        """
        assert self.pushed is not None
        self.lemmas = self.pushed.lemmas  # maybe we should store lemmas incrementally?
        self.goals = self.pushed.goals
        self.pushed = self.pushed.pushed
        return self.top_goal()

    def search(self, *args, at=None, db={}):
        """
        Search the lemma database for things that may match the current goal.

        >>> import kdrag.theories.nat as nat
        >>> n = smt.Const("n", nat.Nat)
        >>> l = Lemma(smt.ForAll([n], nat.Z + n == n))
        >>> ("kdrag.theories.nat.add_Z", nat.add_Z) in l.search().keys()
        True
        >>> ("kdrag.theories.nat.add_S", nat.add_S) in l.search().keys()
        False
        >>> ("kdrag.theories.nat.add_S", nat.add_S) in l.search(nat.add).keys()
        True
        """
        if at is not None:
            return kd.utils.search(self.top_goal().ctx[at], db=db)
        if len(args) == 0:
            return kd.utils.search(self.top_goal().goal, db=db)
        else:
            return kd.utils.search(*args, db=db)

    def fixes(self, prefixes=None) -> list[smt.ExprRef]:
        """fixes opens a forall quantifier. ?|= forall x, p(x) becomes x ?|= p(x)

        >>> x,y = smt.Ints("x y")
        >>> l = Lemma(kd.QForAll([x,y], y >= 0, x + y >= x))
        >>> _x, _y = l.fixes()
        >>> l
        [x!..., y!...] ?|= Implies(y!... >= 0, x!... + y!... >= x!...)
        >>> _x, _y
        (x!..., y!...)
        >>> _x.eq(x)
        False
        >>> Lemma(kd.QForAll([x,y], x >= 0)).fixes("z w")
        [z!..., w!...]
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if isinstance(goal, smt.QuantifierRef) and goal.is_forall():
            self.pop_goal()
            vs, herb_lemma = kd.kernel.herb(goal, prefixes)
            # self.add_lemma(herb_lemma)
            newgoal = herb_lemma.thm.arg(0)

            def cb():
                l = self.get_lemma(smt.Implies(smt.And(ctx), newgoal))
                self.add_lemma(kd.kernel.compose(l, herb_lemma))

            self.goals.append(LemmaCallback(cb, annot=("fixes", goal)))
            self.goals.append(goalctx._replace(sig=goalctx.sig + vs, goal=newgoal))
            return vs
        else:
            raise ValueError(f"fixes tactic failed. Not a forall {goal}")

    def fix(self, prefix=None) -> smt.ExprRef:
        """
        Open a single ForAll quantifier

        >>> x = smt.Int("x")
        >>> l = Lemma(smt.ForAll([x], x != x + 1))
        >>> _x = l.fix()
        >>> l
        [x!...] ; [] ?|= x!... != x!... + 1
        >>> _x.eq(x)
        False
        >>> Lemma(smt.ForAll([x], x != x + 1)).fix("w")
        w!...

        """
        vs = self.fixes(prefixes=prefix)
        if len(vs) > 1:
            raise ValueError("fix tactic failed. More than one variable in quantifier")
        return vs[0]

    def qfix(self, prefix=None) -> smt.ExprRef:
        n = self.fix(prefix=prefix)
        self.intros()
        return n

    def qfixes(self, prefixes=None) -> list[smt.ExprRef]:
        vs = self.fixes(prefixes=prefixes)
        self.intros()
        return vs

    def intros(self) -> smt.ExprRef | list[smt.ExprRef] | Goal:
        """
        intros opens an implication. ?|= p -> q becomes p ?|= q

        >>> p,q,r = smt.Bools("p q r")
        >>> l = Lemma(smt.Implies(p, q))
        >>> l.intros()
        [p] ?|= q
        >>> l = Lemma(smt.Not(q))
        >>> l.intros()
        [q] ?|= False
        """
        goalctx = self.top_goal()
        goal = goalctx.goal
        ctx = goalctx.ctx
        # TODO: Let's remove this
        if isinstance(goal, smt.QuantifierRef) and goal.is_forall():
            return self.fixes()
        self.pop_goal()
        if smt.is_implies(goal):
            self.goals.append(
                goalctx._replace(ctx=ctx + [goal.arg(0)], goal=goal.arg(1))
            )
            return self.top_goal()
        elif smt.is_not(goal):
            self.goals.append(
                goalctx._replace(ctx=ctx + [goal.arg(0)], goal=smt.BoolVal(False))
            )
            return self.top_goal()
        elif smt.is_distinct(goal):
            if goal.num_args() != 2:
                raise NotImplementedError("Intros only implemented for two arguments")
            else:
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx + [goal.arg(0) == goal.arg(1)], goal=smt.BoolVal(False)
                    )
                )
                return self.top_goal()
        elif (
            smt.is_or(goal) and smt.is_not(goal.arg(0))
        ):  # if implies a -> b gets classically unwound to Or(Not(a), b). TODO: Maybe I should remove this
            if goal.num_args() == 2:
                self.goals.append(
                    goalctx._replace(ctx=ctx + [goal.arg(0).arg(0)], goal=goal.arg(1))
                )
            else:
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx + [goal.arg(0).arg(0)], goal=smt.Or(goal.children()[1:])
                    )
                )
            return self.top_goal()
        else:
            raise ValueError("Intros failed.")

    def assumes(self, hyp: smt.BoolRef):
        """

        >>> p,q = smt.Bools("p q")
        >>> l = Lemma(smt.Implies(p, q))
        >>> l.assumes(p)
        [p] ?|= q
        """
        goalctx = self.intros()
        assert isinstance(goalctx, Goal)
        if goalctx.ctx[-1].eq(hyp):
            return goalctx
        else:
            raise ValueError("hypotheses does not match", hyp, goalctx.ctx[-1])

    def simp(self, at=None, unfold=False, path=None) -> "ProofState":
        """
        Use built in z3 simplifier. May be useful for boolean, arithmetic, lambda, and array simplifications.

        >>> x,y = smt.Ints("x y")
        >>> l = Lemma(x + y == y + x)
        >>> l.simp()
        [] ?|= True
        >>> l = Lemma(x == 3 + y + 7)
        >>> l.simp()
        [] ?|= x == 10 + y
        >>> l = Lemma(smt.Lambda([x], x + 1)[3] == y)
        >>> l.simp()
        [] ?|= 4 == y
        >>> l = Lemma(1 + ((2 + smt.IntVal(4)) + 3))
        >>> l.simp(path=[1,0])
        [] ?|= 1 + 6 + 3
        """
        goalctx = self.top_goal()
        if at is None:
            oldgoal = goalctx.goal
            if unfold:
                trace = []
                newgoal = kd.rewrite.simp(oldgoal, trace=trace)
                for l in trace:
                    self.add_lemma(l)
            else:
                newgoal = kd.utils.pathmap(smt.simplify, oldgoal, path)
                self.add_lemma(kd.kernel.prove(smt.Eq(oldgoal, newgoal)))
            # if newgoal.eq(oldgoal):
            #    raise ValueError(
            #        "Simplify failed. Goal is already simplified.", oldgoal
            #    )
            self.goals[-1] = goalctx._replace(goal=newgoal)
        else:
            oldctx = goalctx.ctx
            if at < 0:
                at = len(oldctx) + at
            old = oldctx[at]
            new = kd.utils.pathmap(smt.simplify, old, path)
            if new.eq(old):
                raise ValueError("Simplify failed. Ctx is already simplified.")
            self.add_lemma(kd.kernel.prove(old == new))
            self.goals[-1] = goalctx._replace(
                ctx=oldctx[:at] + [new] + oldctx[at + 1 :]
            )
        return self

    def cases(self, t):
        """
        `cases` let's us consider an object by cases.
        We consider whether Bools are True or False
        We consider the different constructors for datatypes

        >>> import kdrag.theories.nat as nat
        >>> x = smt.Const("x", nat.Nat)
        >>> l = Lemma(smt.BoolVal(True))
        >>> l.cases(x)
        [is(Z, x) == True] ?|= True
        >>> l.auto() # next case
        [is(S, x) == True] ?|= True
        """
        goalctx = self.top_goal()
        ctx = goalctx.ctx
        goal = goalctx.goal
        if t.sort() == smt.BoolSort():
            self.pop_goal()
            self.goals.append(
                goalctx._replace(ctx=ctx + [t == smt.BoolVal(False)], goal=goal)
            )
            self.goals.append(
                goalctx._replace(ctx=ctx + [t == smt.BoolVal(True)], goal=goal)
            )
        elif isinstance(t, smt.DatatypeRef):
            self.pop_goal()
            dsort = t.sort()
            for i in reversed(range(dsort.num_constructors())):
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx + [dsort.recognizer(i)(t) == smt.BoolVal(True)],
                        goal=goal,
                    )
                )
        else:
            raise ValueError("Cases failed. Not a bool or datatype")
        return self.top_goal()

    def auto(self, **kwargs) -> "ProofState":
        """
        `auto` discharges a goal using z3. It forwards all parameters to `kd.prove`
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        self.add_lemma(kd.prove(smt.Implies(smt.And(ctx), goal), **kwargs))
        self.pop_goal()
        self.top_goal()  # TODO: This is clearing lemmacallbacks but why do I need to?
        return self

    def obtain(self, n) -> smt.ExprRef | list[smt.ExprRef]:
        """
        obtain opens an exists quantifier in context and returns the fresh eigenvariable.
        `[exists x, p(x)] ?|= goal` becomes `p(x) ?|= goal`
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if n < 0:
            n = len(ctx) + n
        formula = ctx[n]
        if isinstance(formula, smt.QuantifierRef) and formula.is_exists():
            self.pop_goal()
            fs, obtain_lemma = kd.kernel.obtain(formula)
            self.add_lemma(obtain_lemma)
            self.goals.append(
                goalctx._replace(
                    sig=goalctx.sig + fs,
                    ctx=ctx[:n] + [obtain_lemma.thm.arg(1)] + ctx[n + 1 :],
                    goal=goal,
                )
            )
            if len(fs) == 1:
                return fs[0]
            else:
                return fs
        else:
            raise ValueError("obtain failed. Not an exists")

    def specialize(self, n, *ts):
        """
        Instantiate a universal quantifier in the context.

        >>> x,y = smt.Ints("x y")
        >>> l = Lemma(smt.Implies(smt.ForAll([x],x == y), True))
        >>> l.intros()
        [ForAll(x, x == y)] ?|= True
        >>> l.specialize(0, smt.IntVal(42))
        [ForAll(x, x == y), 42 == y] ?|= True
        """
        goalctx = self.top_goal()
        thm = goalctx.ctx[n]
        if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
            l = kd.kernel.specialize(ts, thm)
            self.add_lemma(l)
            self.goals[-1] = goalctx._replace(ctx=goalctx.ctx + [l.thm.arg(1)])
            return self
        else:
            raise ValueError("Specialize failed. Not a forall", thm)

    def ext(self, at=None):
        """
        Apply extensionality to a goal

        >>> x = smt.Int("x")
        >>> l = Lemma(smt.Lambda([x], smt.IntVal(1)) == smt.K(smt.IntSort(), smt.IntVal(1)))
        >>> _ = l.ext()
        """
        goalctx = self.top_goal()
        if at is None:
            target = goalctx.goal
        else:
            target = goalctx.ctx[at]
        if smt.is_eq(target):
            lhs = target.arg(0)
            if smt.is_func(lhs):
                return self.rw(
                    kd.kernel.ext(smt.domains(lhs), smt.codomain(lhs)), at=at
                )
            else:
                raise ValueError("Ext failed. Target is not an array equality", target)
        else:
            raise ValueError("Ext failed. Target is not an equality", target)

    def split(self, at=None) -> "ProofState":
        """
        `split` breaks apart an `And` or bi-implication `==` goal.
        The optional keyword at allows you to break apart an And or Or in the context

        >>> p = smt.Bool("p")
        >>> l = Lemma(smt.And(True,p))
        >>> l.split()
        [] ?|= True
        >>> l.auto() # next goal
        [] ?|= p
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if at is None:
            if smt.is_and(goal):
                self.pop_goal()
                children = goal.children()
                self.push_lemmas()

                def cb():
                    subproofs = [
                        self.get_lemma(smt.Implies(smt.And(ctx), g)) for g in children
                    ]
                    self.pop_lemmas()
                    self.add_lemma(kd.kernel.andI(subproofs))

                self.goals.append(LemmaCallback(cb, annot=("split", goal)))
                self.goals.extend(
                    [goalctx._replace(ctx=ctx, goal=c) for c in reversed(children)]
                )
            elif smt.is_eq(goal):
                self.pop_goal()
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx, goal=smt.Implies(goal.arg(1), goal.arg(0))
                    )
                )
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx, goal=smt.Implies(goal.arg(0), goal.arg(1))
                    )
                )
            elif smt.is_distinct(goal):
                self.pop_goal()
                for i in range(goal.num_args()):
                    for j in range(i):
                        self.goals.append(
                            goalctx._replace(
                                ctx=ctx + [smt.Eq(goal.arg(j), goal.arg(i))],
                                goal=smt.BoolVal(False),
                            )
                        )
            else:
                raise ValueError("Unexpected case in goal for split tactic", goal)
            return self
        else:
            if at < 0:
                at = len(ctx) + at
            if smt.is_or(ctx[at]):
                self.pop_goal()
                for c in ctx[at].children():
                    self.goals.append(
                        goalctx._replace(ctx=ctx[:at] + [c] + ctx[at + 1 :], goal=goal)
                    )
            elif smt.is_and(ctx[at]):
                self.pop_goal()
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx[:at] + ctx[at].children() + ctx[at + 1 :], goal=goal
                    )
                )
            else:
                raise ValueError("Split failed")
            return self

    def left(self, n=0):
        """
        Select the left case of an `Or` goal.
        Since we're working classically, the other cases are negated and added to the context.

        >>> p,q,r = smt.Bools("p q r")
        >>> l = Lemma(smt.Or(p,q))
        >>> l.left()
        [Not(q)] ?|= p
        >>> l = Lemma(smt.Or(p,q,r))
        >>> l.left(1)
        [Not(p), Not(r)] ?|= q
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if smt.is_or(goal):
            children = goal.children()
            newgoal = children.pop(n)
            self.goals[-1] = goalctx._replace(
                ctx=ctx + list(map(smt.Not, children)), goal=newgoal
            )
            return self.top_goal()
        else:
            raise ValueError("Left failed. Not an or")

    def right(self):
        """
        Select the right case of an `Or` goal.
        Since we're working classically, the other cases are negated and added to the context.

        >>> p,q = smt.Bools("p q")
        >>> l = Lemma(smt.Or(p,q))
        >>> l.right()
        [Not(p)] ?|= q
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if smt.is_or(goal):
            children = goal.children()
            self.goals[-1] = goalctx._replace(
                ctx=ctx + list(map(smt.Not, children[:-1])), goal=children[-1]
            )
            return self.top_goal()
        else:
            raise ValueError("Right failed. Not an or")

    def exists(self, *ts) -> "ProofState":
        """
        Give terms `ts` to satisfy an exists goal
        `?|= exists x, p(x)` becomes `?|= p(ts)`

        >>> x,y = smt.Ints("x y")
        >>> Lemma(smt.Exists([x], x == y)).exists(y)
        [] ?|= y == y
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        assert isinstance(goal, smt.QuantifierRef) and goal.is_exists()
        lemma = kd.kernel.forget(ts, goal)
        self.add_lemma(lemma)
        self.goals[-1] = goalctx._replace(ctx=ctx, goal=lemma.thm.arg(0))
        return self

    def rw(
        self, rule: kd.kernel.Proof | int, at=None, rev=False, **kwargs
    ) -> "ProofState":
        """
        `rewrite` allows you to apply rewrite rule (which may either be a Proof or an index into the context) to the goal or to the context.

        >>> x = kd.FreshVar("x", smt.RealSort())
        >>> pf = kd.prove(smt.Implies(x >= 0, smt.Sqrt(x) ** 2 == x)).forall([x])
        >>> l = Lemma(smt.Implies(x >= 0, smt.Sqrt(x + 2)**2 == x + 2))
        >>> l.intros()
        [x!... >= 0] ?|= ((x!... + 2)**(1/2))**2 == x!... + 2
        >>> l.rw(pf,by=[])
        [x!... >= 0, x!... + 2 >= 0] ?|= x!... + 2 == x!... + 2
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if isinstance(rule, int):
            rulethm = ctx[rule]
        elif kd.kernel.is_proof(rule):
            rulethm = rule.thm
        else:
            raise ValueError(
                "Rewrite tactic failed. Not a proof or context index", rule
            )
        if isinstance(rulethm, smt.QuantifierRef) and rulethm.is_forall():
            vs, body = kd.utils.open_binder(rulethm)
        else:
            vs = []
            body = rulethm
        if smt.is_implies(body):
            cond, body = body.children()
        else:
            cond = None
        if smt.is_eq(body):
            lhs, rhs = body.arg(0), body.arg(1)
            if rev:
                lhs, rhs = rhs, lhs
        else:
            raise ValueError(f"Rewrite tactic failed. Not an equality {rulethm}")
        if at is None:
            target = goal
        elif isinstance(at, int):
            target = ctx[at]
        else:
            raise ValueError(
                "Rewrite tactic failed. `at` is not an index into the context"
            )
        t_subst = kd.utils.pmatch_rec(vs, lhs, target)
        if t_subst is None:
            raise ValueError(
                f"Rewrite tactic failed to apply lemma {rulethm} to target {target}"
            )
        else:
            self.pop_goal()
            lhs1, subst = t_subst
            rhs1 = smt.substitute(rhs, *[(v, t) for v, t in subst.items()])
            target: smt.BoolRef = smt.substitute(target, (lhs1, rhs1))
            if isinstance(rulethm, smt.QuantifierRef) and rulethm.is_forall():
                self.add_lemma(kd.kernel.specialize([subst[v] for v in vs], rulethm))
            if not isinstance(rule, int) and kd.kernel.is_proof(rule):
                self.add_lemma(rule)
            if at is None:
                self.goals.append(goalctx._replace(ctx=ctx, goal=target))
            else:
                if at == -1:
                    at = len(ctx) - 1
                self.goals.append(
                    goalctx._replace(ctx=ctx[:at] + [target] + ctx[at + 1 :], goal=goal)
                )
            if cond is not None:
                return self.have(
                    smt.substitute(cond, *[(v, t) for v, t in subst.items()]), **kwargs
                )
            else:
                return self

    def symm(self):
        """
        Swap left and right hand side of equational goal

        >>> x,y = smt.Ints("x y")
        >>> Lemma(x == y).symm()
        [] ?|= y == x
        """
        ctxgoal = self.top_goal()
        if smt.is_eq(ctxgoal.goal):
            self.goals[-1] = ctxgoal._replace(
                goal=smt.Eq(ctxgoal.goal.arg(1), ctxgoal.goal.arg(0))
            )
            return self.top_goal()
        else:
            raise ValueError("Symm tactic failed. Not an equality", ctxgoal.goal)

    def eq(self, rhs: smt.ExprRef, **kwargs):
        """replace rhs in equational goal"""
        # TODO: consider allow `by` keyword to reference context`
        ctxgoal = self.top_goal()
        if smt.is_eq(ctxgoal.goal):
            self.add_lemma(
                kd.kernel.prove(
                    smt.Implies(smt.And(ctxgoal.ctx), ctxgoal.goal.arg(1) == rhs),
                    **kwargs,
                )
            )
            self.goals[-1] = ctxgoal._replace(goal=smt.Eq(ctxgoal.goal.arg(0), rhs))
            return self.top_goal()
        else:
            raise ValueError("Eq tactic failed. Not an equality", ctxgoal.goal)

    def newgoal(self, newgoal: smt.BoolRef, **kwargs):
        """
        Try to show newgoal is sufficient to prove current goal
        """
        goalctx = self.top_goal()
        self.add_lemma(
            kd.prove(
                smt.Implies(smt.And(goalctx.ctx + [newgoal]), goalctx.goal), **kwargs
            )
        )
        self.goals[-1] = goalctx._replace(goal=newgoal)
        return self.top_goal()

    def beta(self, at=None):
        """
        Perform beta reduction on goal or context

        >>> x = smt.Int("x")
        >>> l = Lemma(smt.Lambda([x], x + 1)[3] == 4)
        >>> l.beta()
        [] ?|= 3 + 1 == 4
        >>> l = Lemma(smt.Implies(smt.Lambda([x], x + 1)[3] == 5, True))
        >>> l.intros()
        [Lambda(x, x + 1)[3] == 5] ?|= True
        >>> l.beta(at=0)
        [3 + 1 == 5] ?|= True
        """
        goalctx = self.top_goal()
        if at is None:
            oldgoal = goalctx.goal
            newgoal = kd.rewrite.beta(oldgoal)
            if newgoal.eq(oldgoal):
                raise ValueError(
                    "Beta tactic failed. Goal is already beta reduced.", oldgoal
                )
            self.add_lemma(kd.kernel.prove(smt.Eq(oldgoal, newgoal)))
            self.goals[-1] = goalctx._replace(goal=newgoal)
        else:
            oldctx = goalctx.ctx
            old = oldctx[at]
            new = kd.rewrite.beta(old)
            if new.eq(old):
                raise ValueError(
                    "Beta tactic failed. Ctx is already beta reduced.", old
                )
            self.add_lemma(kd.kernel.prove(old == new))
            self.goals[-1] = goalctx._replace(
                ctx=oldctx[:at] + [new] + oldctx[at + 1 :]
            )
        return self.top_goal()

    def unfold(self, *decls: smt.FuncDeclRef, at=None) -> "ProofState":
        """
        Unfold all definitions once. If declarations are given, only those are unfolded.

        >>> import kdrag.theories.nat as nat
        >>> l = Lemma(nat.Z + nat.Z == nat.Z)
        >>> l
        [] ?|= add(Z, Z) == Z
        >>> l.unfold(nat.double) # does not unfold add
        [] ?|= add(Z, Z) == Z
        >>> l.unfold()
        [] ?|= If(is(Z, Z), Z, S(add(pred(Z), Z))) == Z
        """
        assert all(isinstance(d, smt.FuncDeclRef) for d in decls)
        goalctx = self.top_goal()
        decls1 = None if len(decls) == 0 else decls
        if at is None:
            e = goalctx.goal
            trace = []
            e2 = kd.rewrite.unfold(e, decls=decls1, trace=trace)
            for lem in trace:
                self.add_lemma(lem)
            self.pop_goal()
            self.goals.append(goalctx._replace(goal=e2))
        else:
            e = goalctx.ctx[at]
            trace = []
            e2 = kd.rewrite.unfold(e, decls=decls, trace=trace)
            self.add_lemma(kd.prove(e == e2, by=trace))
            self.pop_goal()
            if at == -1:
                at = len(goalctx.ctx) - 1
            self.goals.append(
                goalctx._replace(ctx=goalctx.ctx[:at] + [e2] + goalctx.ctx[at + 1 :])
            )

        return self

    def apply(self, pf: kd.kernel.Proof | int):
        """
        `apply` matches the conclusion of a proven clause

        >>> x,y = smt.Ints("x y")
        >>> l = kd.Lemma(smt.Implies(smt.Implies(x == 7, y == 3), y == 3))
        >>> l.intros()
        [Implies(x == 7, y == 3)] ?|= y == 3
        >>> l.apply(0)
        [Implies(x == 7, y == 3)] ?|= x == 7

        >>> mylemma = kd.prove(kd.QForAll([x], x > 1, x > 0))
        >>> kd.Lemma(x > 0).apply(mylemma)
        [] ?|= x > 1

        >>> p,q = smt.Bools("p q")
        >>> l = kd.Lemma(smt.Implies(smt.Not(p), q))
        >>> l.intros()
        [Not(p)] ?|= q
        >>> l.apply(0)
        [Not(q)] ?|= p
        """
        goalctx = self.top_goal()
        ctx, goal = goalctx.ctx, goalctx.goal
        if isinstance(pf, int):
            thm = ctx[pf]
            if smt.is_not(thm):
                # Not(p) is spiritually a `p -> False`
                self.pop_goal()
                newctx = ctx.copy()
                newctx.pop(pf)
                newctx.append(smt.Not(goal))
                self.goals.append(goalctx._replace(ctx=newctx, goal=thm.arg(0)))
                return self.top_goal()
        elif isinstance(pf, kd.Proof):
            thm = pf.thm
        else:
            raise ValueError("Apply tactic failed. Not a proof or context index", thm)
        rule = kd.rewrite.rule_of_expr(thm)
        substgoal = kd.rewrite.backward_rule(rule, goal)
        if substgoal is None:
            raise ValueError(
                f"Apply tactic failed to apply lemma {thm} to goal {goal} "
            )
        else:
            subst, newgoal = substgoal
            if isinstance(pf, kd.Proof) and len(rule.vs) > 0:
                pf1 = kd.kernel.instan([subst[v] for v in rule.vs], pf)
                self.add_lemma(pf1)
            elif isinstance(pf, kd.Proof) and len(rule.vs) == 0:
                self.add_lemma(pf)
            elif isinstance(pf, int) and len(rule.vs) > 0:
                pf1 = kd.kernel.specialize([subst[v] for v in rule.vs], ctx[pf])
                self.add_lemma(pf1)
            self.goals[-1] = goalctx._replace(ctx=ctx, goal=newgoal)
            return self.top_goal()

    def induct(
        self,
        x: smt.ExprRef,
        using: Optional[
            Callable[
                [smt.ExprRef, Callable[[smt.ExprRef, smt.BoolRef], smt.BoolRef]],
                kd.kernel.Proof,
            ]
        ] = None,
    ):
        """
        Apply an induction lemma instantiated on x.
        """
        goal = self.top_goal().goal
        if using is None:
            indlem = x.induct(smt.Lambda([x], goal))
        else:
            indlem = using(x, smt.Lambda([x], goal))
        self.add_lemma(indlem)
        self.apply(indlem)
        if smt.is_and(self.top_goal().goal):
            # self.split()
            goalctx = self.pop_goal()
            self.goals.extend(
                [goalctx._replace(goal=c) for c in reversed(goalctx.goal.children())]
            )
        return self.top_goal()

    def contra(self):
        """
        Prove the goal by contradiction.

        >>> p = smt.Bool("p")
        >>> l = Lemma(p)
        >>> l.contra()
        [Not(p)] ?|= False
        """
        goalctx = self.pop_goal()
        self.goals.append(
            goalctx._replace(
                ctx=goalctx.ctx + [smt.Not(goalctx.goal)], goal=smt.BoolVal(False)
            )
        )
        return self.top_goal()

    def clear(self, n: int):
        """
        Remove a hypothesis from the context
        """
        ctxgoal = self.pop_goal()
        ctx = ctxgoal.ctx.copy()
        ctx.pop(n)
        self.goals.append(ctxgoal._replace(ctx=ctx))
        return self.top_goal()

    def generalize(self, *vs: smt.ExprRef):
        """
        Put variables forall quantified back on goal. Useful for strengthening induction hypotheses.
        """
        goalctx = self.top_goal()
        self.pop_goal()
        self.add_lemma(kd.kernel.specialize(vs, smt.ForAll(vs, goalctx.goal)))
        self.goals.append(goalctx._replace(goal=smt.ForAll(vs, goalctx.goal)))
        return self.top_goal()

    def revert(self, n: int):
        """
        Move a hypothesis back onto the goal as an implication.
        >>> p,q = smt.Bools("p q")
        >>> l = Lemma(smt.Implies(p, q))
        >>> l.intros()
        [p] ?|= q
        >>> l.revert(0)
        [] ?|= Implies(p, q)
        """
        goalctx = self.top_goal()
        ctx = goalctx.ctx.copy()
        hyp = ctx.pop(n)
        self.pop_goal()
        self.goals.append(
            goalctx._replace(ctx=ctx, goal=smt.Implies(hyp, goalctx.goal))
        )
        return self.top_goal()

    def sublemma(self) -> "ProofState":
        """
        Create a sub ProofState for the current goal. This is useful to break up a proof into smaller lemmas.
        The goal is the same but the internally held `kd.Proof` database is cleared, making it easier for z3
        On calling `'l.qed()`, the sublemma will propagate it's `kd.Proof`  back to it's parent.

        >>> l1 = Lemma(smt.BoolVal(True))
        >>> l2 = l1.sublemma()
        >>> l2
        [] ?|= True
        >>> l2.auto()
        Nothing to do. Hooray!
        >>> l1
        [] ?|= True
        >>> l2.qed()
        |= True
        >>> l1
        Nothing to do. Hooray!
        >>> l1.qed()
        |= True
        """
        goalctx = self.top_goal()
        return ProofState(goalctx, _parent=self)

    def sub(self) -> "ProofState":
        return self.sublemma()

    def __enter__(self) -> "ProofState":
        """
        On entering a `with` block, return self.
        This marks that at the exit of the `with` block, qed will be automatically called
        and `kd.Proof` propagated back to a parent
        """
        if len(self.goals) != 1 or len(self.lemmas[-1]) != 0:
            raise ValueError(
                "Entered a non-fresh ProofState. Did you forget to call l.subproof?"
            )
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """
        On exiting a `with` block, if no exception occurred, call qed and propagate the proof to the parent
        """
        if exc_type is not None:
            return False  # propagate exception
        else:
            if len(self.goals) == 0:
                self.qed()
            else:
                print("Goal", self.top_goal())

    def show(self, thm: smt.BoolRef, **kwargs) -> "ProofState":
        """
        Documents the current goal and discharge it if by keyword is used

        >>> x = smt.Int("x")
        >>> l = Lemma(smt.Implies(x > 0, smt.And(x > -2, x > -1)))
        >>> l.intros()
        [x > 0] ?|= And(x > -2, x > -1)
        >>> l.split()
        [x > 0] ?|= x > -2
        >>> with l.show(x > -2).sub() as sub1:
        ...     _ = sub1.auto()
        >>> l
        [x > 0] ?|= x > -1
        >>> l.show(x > -1, by=[])
        Nothing to do. Hooray!
        >>> l.qed()
        |= Implies(x > 0, And(x > -2, x > -1))
        """
        # TODO: maybe search through goal stack?
        goal = self.top_goal().goal
        if not thm.eq(goal):
            raise ValueError("Goal does not match", thm, goal)
        if len(kwargs) != 0:
            self.auto(**kwargs)
        return self

    def exact(self, pf: kd.kernel.Proof):
        """
        Exact match of goal with given proof

        >>> p = smt.Bool("p")
        >>> l = Lemma(smt.Implies(p, p))
        >>> l.exact(kd.prove(smt.BoolVal(True)))
        Traceback (most recent call last):
            ...
        ValueError: Exact tactic failed. Given: True Expected: Implies(p, p)
        >>> l.exact(kd.prove(smt.Implies(p, p)))
        Nothing to do!
        """
        goalctx = self.top_goal()
        goalexpr = goalctx.to_expr()
        if pf.thm.eq(goalexpr):
            self.add_lemma(pf)
            self.pop_goal()
            return self.top_goal()
        else:
            raise ValueError(
                "Exact tactic failed. Given:", pf.thm, "Expected:", goalexpr
            )

    def assumption(self) -> Goal:
        """
        Exact match of goal in the context
        """
        goalctx = self.pop_goal()
        goal, ctx = goalctx.goal, goalctx.ctx
        if any([goal.eq(h) for h in ctx]):
            return self.top_goal()
        else:
            raise ValueError("Assumption tactic failed", goal, ctx)

    def have(self, conc: smt.BoolRef, **kwargs) -> "ProofState":
        """
        Prove the given formula and add it to the current context

        >>> x = smt.Int("x")
        >>> l = Lemma(smt.Implies(x > 0, x > -2))
        >>> l.intros()
        [x > 0] ?|= x > -2
        >>> l.have(x > -1, by=[])
        [x > 0, x > -1] ?|= x > -2
        >>> l.have(x > 42)
        [x > 0, x > -1] ?|= x > 42
        """
        assert isinstance(conc, smt.BoolRef)
        goalctx = self.pop_goal()
        self.goals.append(goalctx._replace(ctx=goalctx.ctx + [conc]))
        newgoal = goalctx._replace(goal=conc)
        self.goals.append(newgoal)
        if len(kwargs) != 0:
            self.auto(**kwargs)
            # self.add_lemma(
            #    kd.kernel.prove(smt.Implies(smt.And(goalctx.ctx), conc), **kwargs)
            # )
        return self

    def case(self, thm=None) -> "ProofState":
        """
        To make more readable proofs, `case` lets you state which case you are currently in from a `cases`
        It is basically an alias for `have` followed by `clear(-1)`.

        >>> p = smt.Bool("p")
        >>> l = Lemma(smt.Or(p, smt.Not(p)))
        >>> _ = l.cases(p)
        >>> l.case(p)
        [p == True] ?|= Or(p, Not(p))
        >>> _ = l.auto()
        >>> l.case(smt.Not(p))
        [p == False] ?|= Or(p, Not(p))
        """
        if thm is None:
            return self
        else:
            self.have(thm, by=[])  # self.assumption()?
            self.clear(-1)
            return self

    def admit(self) -> Goal:
        """
        admit the current goal without proof. Don't feel bad about keeping yourself moving, but be aware that you're not done.

        >>> l = Lemma(smt.BoolVal(False)) # a false goal
        >>> _ = l.admit()
        Admitting lemma False
        >>> l.qed()
        |= False
        """
        goalctx = self.pop_goal()
        self.add_lemma(kd.kernel.prove(goalctx.goal, admit=True))
        return self.top_goal()

    def repeat(self, f: Callable[[], Goal]) -> Goal:
        """
        >>> p = smt.Bool("p")
        >>> l = Lemma(smt.Implies(p, smt.Implies(p, p)))
        >>> l.intros()
        [p] ?|= Implies(p, p)
        >>> l = Lemma(smt.Implies(p, smt.Implies(p, p)))
        >>> l.repeat(lambda: l.intros())
        [p, p] ?|= p

        """
        g = f()
        while True:
            try:
                g = f()
            except Exception as _:
                return g

    # TODO
    # def suggest():
    # def llm():
    # def calc

    def pop_goal(self) -> Goal:
        goal = self.top_goal()  # to clear possible LemmaCallback
        self.goals.pop()
        return goal

    def top_goal(self) -> Goal:
        while len(self.goals) > 0 and isinstance(self.goals[-1], LemmaCallback):
            lc = self.goals.pop()
            assert isinstance(lc, LemmaCallback)  # for type checker
            try:
                lc.cb()
            except Exception as e:
                raise ValueError("LemmaCallback failed", lc.annot) from e
        if len(self.goals) == 0:
            return Goal.empty()  # kind of hacky
        res = self.goals[-1]
        assert isinstance(res, Goal)
        return res

    def __repr__(self):
        if len(self.goals) == 0:
            return "Nothing to do. Hooray!"
        return repr(self.top_goal())

    def qed(self, **kwargs) -> kd.kernel.Proof:
        """
        return the actual final `Proof` of the lemma that was defined at the beginning.
        """
        for lam_cb in reversed(self.goals):
            if isinstance(lam_cb, LemmaCallback):
                try:
                    lam_cb.cb()
                except Exception as e:
                    raise ValueError("LemmaCallback failed", lam_cb.annot) from e
        thm = self.thm.to_expr()
        pf0 = self.lemmas[-1].get(thm.get_id())
        if pf0 is not None:
            return pf0
        if "by" in kwargs:
            kwargs["by"].extend(self.lemmas[-1].values())
        else:
            kwargs["by"] = list(self.lemmas[-1].values())
        pf = kd.kernel.prove(thm, **kwargs)
        kdrag.config.perf_event(
            "ProofState", self.thm, time.perf_counter() - self.start_time
        )
        if self._parent is not None:
            self._parent.exact(pf)
        return pf


_TRUE = kd.kernel.prove(smt.BoolVal(True))


def Theorem(
    goal: smt.BoolRef | str,
) -> Callable[[Callable[[ProofState], None]], kd.kernel.Proof]:
    """
    A decorator to create a theorem from a function that takes a `ProofState` as argument.

    >>> x = smt.Int("x")
    >>> @Theorem(x + 1 > x)
    ... def mytheorem(l: ProofState):
    ...     "An example theorem"
    ...     l.auto()
    >>> mytheorem
    |= x + 1 > x
    >>> mytheorem.__doc__
    'An example theorem'
    >>> @Theorem("forall (x : Int), x + 1 > x")
    ... def mytheorem2(l: ProofState):
    ...     l.auto()
    >>> mytheorem2
    |= ForAll(x, x + 1 > x)
    >>> @Theorem("x + 1 > x") # Getting globals from scope
    ... def mytheorem3(l: ProofState):
    ...     l.auto()
    >>> mytheorem3
    |= x + 1 > x
    """
    if isinstance(goal, str):
        l, g = reflect._calling_globals_locals()
        goal1 = microlean.parse(goal, g)
    else:
        goal1 = goal
    assert isinstance(goal1, smt.BoolRef)

    def res(f: Callable[[ProofState], None]) -> kd.kernel.Proof:
        l = kd.Lemma(goal1)
        f(l)
        pf = l.qed()
        # To override metadata of the returned proof
        # Proof is frozen, so this is a bit fishy
        # @functools.update_wrapper had assumptions about return type being a function
        object.__setattr__(pf, "__doc__", getattr(f, "__doc__", None))
        object.__setattr__(pf, "__module__", getattr(f, "__module__", None))
        object.__setattr__(pf, "__name__", getattr(f, "__name__", None))
        object.__setattr__(pf, "__qualname__", getattr(f, "__qualname__", None))
        return pf

    return res


def PTheorem(
    goal: smt.BoolRef | str,
):
    """
    A decorator to create a theorem from a function that takes a `ProofState` as argument.

    >>> x = smt.Int("x")
    >>> @PTheorem(x + 1 > x)
    ... def mytheorem(l: ProofState):
    ...     "An example theorem"
    ...     l.auto()
    Lemma Complete! Change PTheorem to Theorem
    """
    if isinstance(goal, str):
        l, g = reflect._calling_globals_locals()
        goal1 = microlean.parse(goal, g)
    else:
        goal1 = goal
    assert isinstance(goal1, smt.BoolRef)

    def res(f: Callable[[ProofState], None]) -> None:
        l = kd.Lemma(goal1)
        f(l)
        if len(l.goals) == 0:
            l.qed()
            print("Lemma Complete! Change PTheorem to Theorem")
        else:
            print("Next Goal:\n", l.top_goal())

    return res
