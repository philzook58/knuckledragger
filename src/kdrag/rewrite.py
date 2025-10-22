"""
Utilities for rewriting and simplification including pattern matching and unification.
"""

import kdrag.smt as smt
import kdrag as kd
from enum import Enum
from typing import NamedTuple, Optional, Sequence
import kdrag.utils as utils
from collections import defaultdict


def simp1(t: smt.ExprRef) -> smt.ExprRef:
    """simplify a term using z3 built in simplifier"""
    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
    G = smt.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = smt.Then(smt.Tactic("demodulator"), smt.Tactic("simplify")).apply(G)[0]
    # TODO make this extraction more robust
    return G2[len(G2) - 1].children()[1]


def simp2(t: smt.ExprRef) -> smt.ExprRef:
    """simplify a term using z3 built in simplifier"""
    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
    G = smt.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = smt.Tactic("elim-predicates").apply(G)[0]
    return G2[len(G2) - 1].children()[1]


# TODO: Doesn't seem to do anything?
# def factor(t: smt.ExprRef) -> smt.ExprRef:
#    """factor a term using z3 built in tactic"""
#    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
#    G = smt.Goal()
#    for v in kd.kernel.defns.values():
#        G.add(v.ax.thm)
#    G.add(expr == t)
#    G2 = smt.Tactic("factor").apply(G)[0]
#    return G2[len(G2) - 1].children()[1]


def unfold(
    e: smt.ExprRef, decls: Optional[Sequence[smt.FuncDeclRef]] = None, trace=None
) -> smt.ExprRef:
    """
    >>> x = smt.Int("x")
    >>> f = kd.define("f", [x], x + 42)
    >>> trace = []
    >>> unfold(f(1), trace=trace)
    1 + 42
    >>> trace
    [|= f(1) == 1 + 42]

    >>> unfold(smt.Lambda([x], f(x)))
    Lambda(x, x + 42)
    """
    if decls is None:
        decls = kd.utils.defined_decls(e)
    if len(decls) == 0:
        return e
    e1, pf = kd.kernel.unfold(e, decls=decls)
    if trace is not None and not e1.eq(e):
        trace.append(pf)
    return e1


def beta(e: smt.ExprRef) -> smt.ExprRef:
    """
    Do one pass of beta normalization.

    >>> x = smt.Int("x")
    >>> y = smt.String("y")
    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort())
    >>> beta(f(x))
    f(x)
    >>> beta(f(smt.Lambda([x], f(x))[1]))
    f(f(1))
    >>> beta(f(smt.Select(smt.Lambda([x,y], x), 1, smt.StringVal("fred"))))
    f(1)
    """
    if (
        smt.is_select(e)
        and isinstance(e.arg(0), smt.QuantifierRef)
        and e.arg(0).is_lambda()
    ):
        args = [beta(c) for c in e.children()[1:]]
        f = e.arg(0)
        return smt.substitute_vars(f.body(), *reversed(args))
    elif smt.is_app(e):
        decl = e.decl()
        children = [beta(c) for c in e.children()]
        return decl(*children)
    elif isinstance(e, smt.QuantifierRef):
        vs, e1 = kd.utils.open_binder_unhygienic(e)
        if e.is_forall():
            return smt.ForAll(vs, beta(e1))
        elif e.is_exists():
            return smt.Exists(vs, beta(e1))
        elif e.is_lambda():
            return smt.Lambda(vs, beta(e1))
        else:
            raise Exception("Unexpected quantifier", e)
    else:
        raise Exception("Unexpected term", e)


def full_simp(e: smt.ExprRef, trace=None) -> smt.ExprRef:
    """
    Fully simplify using definitions and built in z3 simplifier until no progress is made.

    >>> import kdrag.theories.nat as nat
    >>> full_simp(nat.one + nat.one + nat.S(nat.one))
    S(S(S(S(Z))))

    >>> p = smt.Bool("p")
    >>> full_simp(smt.If(p, 42, 3))
    If(p, 42, 3)
    """
    while True:
        e = unfold(e, trace=trace)
        e1 = smt.simplify(e)
        if e1.eq(e):
            return e
        else:
            e = e1


def simp(e: smt.ExprRef, trace=None, max_iter=3) -> smt.ExprRef:
    """
    Simplify using definitions and built in z3 simplifier until no progress is made.

    >>> import kdrag.theories.nat as nat
    >>> simp(nat.one + nat.one + nat.S(nat.one))
    S(S(S(S(Z))))

    >>> p = smt.Bool("p")
    >>> simp(smt.If(p, 42, 3))
    If(p, 42, 3)
    """
    i = 0
    ebest = e
    bestsize = len(e.sexpr())
    while True:
        i += 1
        if max_iter is not None and i > max_iter:
            return ebest
        e = unfold(e, trace=trace)
        if (newsize := len(e.sexpr())) < bestsize:
            ebest = e
            bestsize = newsize
        # TODO: Interesting options: som, sort_store, elim_ite, flat, split_concat_eq, sort_sums, sort_disjunctions
        e1 = smt.simplify(e)
        if (newsize := len(e1.sexpr())) < bestsize:
            ebest = e1
            bestsize = newsize
        if e1.eq(e):
            return ebest
        else:
            if trace is not None:
                trace.append(kd.kernel.prove(smt.Eq(e, e1)))
            e = e1


def esimp(vs: list[smt.ExprRef], goal: smt.BoolRef, max_iters=7, timeout=50):
    """
    Simplify and unfold goal while seeking a ground model for vs that is provably a solution.
    This can be used in a minikanren-lite way or to produce counterexamples.
    Does not produce generalized solutions like a prolog would.

    >>> n,x,y = smt.Ints("n x y")
    >>> fact = smt.Function("fact", smt.IntSort(), smt.IntSort())
    >>> fact = kd.define("fact", [n], smt.If(n <= 0, 1, n * fact(n - 1)))
    >>> esimp([x], fact(x) == 6)
    {x: 3}
    """
    for i in range(max_iters):
        goal0 = goal
        goal = smt.simplify(goal)
        goal1 = unfold(goal)
        assert isinstance(goal1, smt.BoolRef)  # type checker
        goal = goal1
        s = smt.Solver()
        s.set("timeout", timeout)
        s.add(goal)
        res = s.check()
        if res == smt.unsat:
            return False  # Can't be satisfied. raise?
        elif res == smt.sat:
            # Do loop or generalize here?
            m = s.model()
            subst = {v: m.eval(v) for v in vs}
            sgoal = smt.substitute(goal, *subst.items())
            s = smt.Solver()
            s.set("timeout", timeout)
            s.add(smt.Not(sgoal))
            res = s.check()
            if res == smt.unsat:
                return subst
            else:
                # still satisfiable. Not provably a solution.
                pass
        if goal0.eq(goal):
            # No progress. TODO: Could start eliminating models at this point.
            return None


def def_eq(e1: smt.ExprRef, e2: smt.ExprRef, trace=None) -> bool:
    """
    A notion of computational equality. Unfold and simp.

    >>> import kdrag.theories.nat as nat
    >>> def_eq(nat.one + nat.one, nat.S(nat.S(nat.Z)))
    True
    """
    e1 = simp(e1, trace=trace)
    e2 = simp(e2, trace=trace)
    return kd.utils.alpha_eq(e1, e2)
    """
    TODO: But we can have early stopping if we do these processes interleaved.
    Do each step and keep list of seen ids.
    while not e1.eq(e2):
        e1 = unfold(e1, trace=trace)
        e2 = unfold(e2, trace=trace)
    """


def rewrite1(
    t: smt.ExprRef, vs: list[smt.ExprRef], lhs: smt.ExprRef, rhs: smt.ExprRef
) -> Optional[smt.ExprRef]:
    """
    Rewrite at root a single time.
    """
    subst = utils.pmatch(vs, lhs, t)
    if subst is not None:
        return smt.substitute(rhs, *subst.items())
    return None


def apply(
    goal: smt.BoolRef, vs: list[smt.ExprRef], head: smt.BoolRef, body: smt.BoolRef
) -> Optional[smt.BoolRef]:
    res = rewrite1(goal, vs, head, body)
    assert res is None or isinstance(res, smt.BoolRef)
    return res


class RewriteRule(NamedTuple):
    """A rewrite rule tuple"""

    vs: list[smt.ExprRef]
    lhs: smt.ExprRef
    rhs: smt.ExprRef
    pf: Optional[kd.kernel.Proof] = None

    def freshen(self) -> "RewriteRule":
        """Freshen the rule by renaming variables.

        >>> x,y= smt.Reals("x y")
        >>> rule = RewriteRule([x,y], x*y, y*x)
        >>> rule.freshen()
        RewriteRule(vs=[x..., y...], lhs=x...*y..., rhs=y...*x..., pf=None)
        """
        vs1 = [smt.FreshConst(v.sort(), prefix=v.decl().name()) for v in self.vs]
        return RewriteRule(
            vs1,
            lhs=smt.substitute(self.lhs, *zip(self.vs, vs1)),
            rhs=smt.substitute(self.rhs, *zip(self.vs, vs1)),
            pf=self.pf,
        )

    def to_expr(self) -> smt.BoolRef | smt.QuantifierRef:
        """Convert the rule to a theorem of form `forall vs, lhs = rhs`.

        >>> x,y = smt.Reals("x y")
        >>> RewriteRule([x,y], x*y, y*x).to_expr()
        ForAll([x, y], x*y == y*x)
        """
        if len(self.vs) == 0:
            return smt.Eq(self.lhs, self.rhs)
        else:
            return smt.ForAll(self.vs, smt.Eq(self.lhs, self.rhs))

    @classmethod
    def from_expr(
        cls, expr: smt.BoolRef | smt.QuantifierRef | kd.kernel.Proof
    ) -> "RewriteRule":
        """Convert a theorem of form `forall vs, lhs = rhs` to a rule."""
        return rewrite_of_expr(expr)


def rewrite1_rule(
    t: smt.ExprRef,
    rule: RewriteRule,
    trace: Optional[list[tuple[RewriteRule, dict[smt.ExprRef, smt.ExprRef]]]] = None,
) -> Optional[smt.ExprRef]:
    """
    Rewrite at root a single time.
    """
    subst = utils.pmatch(rule.vs, rule.lhs, t)
    if subst is not None:
        if trace is not None:
            trace.append((rule, subst))
        return smt.substitute(rule.rhs, *subst.items())
    return None


def rewrite_once(t: smt.ExprRef, rules: list[RewriteRule], trace=None) -> smt.ExprRef:
    """
    Sweep through term once performing rewrites.

    >>> x = smt.Real("x")
    >>> rule = RewriteRule([x], x**2, x*x)
    >>> rewrite_once((x**2)**2, [rule])
    x*x*x*x
    """
    if smt.is_app(t):
        t = t.decl()(
            *[rewrite_once(arg, rules) for arg in t.children()]
        )  # rewrite children
        for rule in rules:
            res = rewrite1_rule(t, rule, trace=trace)
            if res is not None:
                t = res
    return t


class RewriteRuleException(Exception): ...


def rewrite_of_expr(
    thm: smt.BoolRef | smt.QuantifierRef | kd.kernel.Proof,
) -> RewriteRule:
    """
    Unpack theorem of form `forall vs, lhs = rhs` into a Rule tuple

    >>> x = smt.Real("x")
    >>> rewrite_of_expr(smt.ForAll([x], x**2 == x*x))
    RewriteRule(vs=[X...], lhs=X...**2, rhs=X...*X...)
    """
    vs = []
    thm1 = thm  # to help out pyright
    if isinstance(thm, kd.kernel.Proof):
        thm1 = thm.thm
    while isinstance(thm1, smt.QuantifierRef):
        if thm1.is_forall():
            vs1, thm1 = utils.open_binder(thm1)
            vs.extend(vs1)
        else:
            raise RewriteRuleException("Not a universal quantifier", thm1)
    if not smt.is_eq(thm1):
        raise RewriteRuleException("Not an equation", thm)
    assert isinstance(thm1, smt.ExprRef)  # pyright
    lhs, rhs = thm1.children()
    return RewriteRule(
        vs, lhs, rhs, pf=thm if isinstance(thm, kd.kernel.Proof) else None
    )


def decl_index(rules: list[RewriteRule]) -> dict[smt.FuncDeclRef, RewriteRule]:
    """Build a dictionary of rules indexed by their lhs head function declaration."""
    return {rule.lhs.decl(): rule for rule in rules}


def rewrite_slow(
    t: smt.ExprRef,
    rules: list[smt.BoolRef | smt.QuantifierRef | kd.kernel.Proof],
    trace=None,
) -> smt.ExprRef:
    """
    Repeat rewrite until no more rewrites are possible.

    >>> x,y,z = smt.Reals("x y z")
    >>> unit = kd.prove(smt.ForAll([x], x + 0 == x))
    >>> x + 0 + 0 + 0 + 0
    x + 0 + 0 + 0 + 0
    >>> rewrite(x + 0 + 0 + 0 + 0, [unit])
    x
    """
    rules1 = [
        rule if isinstance(rule, RewriteRule) else rewrite_of_expr(rule)
        for rule in rules
    ]
    while True:
        t1 = rewrite_once(t, rules1, trace=trace)
        if t1.eq(t):
            return t1
        t = t1


def rewrite(
    t: smt.ExprRef,
    rules: Sequence[smt.BoolRef | smt.QuantifierRef | kd.kernel.Proof | RewriteRule],
    trace=None,
) -> smt.ExprRef:
    """
    Repeat rewrite until no more rewrites are possible.

    >>> x,y,z = smt.Reals("x y z")
    >>> unit = kd.prove(smt.ForAll([x], x + 0 == x))
    >>> x + 0 + 0 + 0 + 0
    x + 0 + 0 + 0 + 0
    >>> rewrite(x + 0 + 0 + 0 + 0, [unit])
    x
    """
    rules1 = [
        rule if isinstance(rule, RewriteRule) else rewrite_of_expr(rule)
        for rule in rules
    ]
    db = defaultdict(list)
    for rule in rules1:
        db[rule.lhs.decl()].append(rule)

    # @functools.cache
    def worker(e):
        while True:
            if smt.is_app(e):
                decl = e.decl()
                children = [worker(c) for c in e.children()]
                e = decl(*children)
                rules = db.get(decl, ())
                done = True
                for rule in rules:
                    res = rewrite1_rule(e, rule, trace=trace)
                    if res is not None:
                        e = res
                        done = False
                        break
                if done:
                    return e
            else:
                return e

    return worker(t)


def all_narrow(
    vs: list[smt.ExprRef], t: smt.ExprRef, lhs: smt.ExprRef, rhs: smt.ExprRef
) -> list[tuple[smt.ExprRef, dict[smt.ExprRef, smt.ExprRef]]]:
    """
    Look for pattern lhs to unify with a subterm of t.
    returns a list of all of those lhs -> rhs applied + the substitution resulting from the unification.
    The substitution is so that we can apply the other `t -> s` rule once we return.


    This helper is asymmettric between t and lhs. You need to call it twice to get all critical pairs.

    >>> x,y,z = smt.Reals("x y z")
    >>> all_narrow([x,y], -(-(-(x))), -(-(y)), y)
    [(y, {y: -x}), (-y, {x: y}), (--y, {x: -y})]
    """
    res = []
    if any(
        t.eq(v) for v in vs
    ):  # Non trivial overlap only `X ~ lhs` is not interesting.
        return res
    subst = kd.utils.unify(vs, t, lhs)
    if subst is not None:
        res.append((rhs, subst))
    f, children = t.decl(), t.children()
    for n, arg in enumerate(children):
        # recurse into subterms and lift result under f if found something
        for s, subst in all_narrow(vs, arg, lhs, rhs):
            args = children[:n] + [s] + children[n + 1 :]
            res.append((f(*args), subst))
    return res


class Rule(NamedTuple):
    vs: list[smt.ExprRef]
    hyp: smt.BoolRef
    conc: smt.BoolRef
    pf: Optional[kd.kernel.Proof] = None

    def freshen(self):
        """Freshen the rule by renaming variables.

        >>> x,y= smt.Reals("x y")
        >>> rule = Rule([x], x > 0, x < 0)
        >>> rule.freshen()
        Rule(vs=[x...], hyp=x... > 0, conc=x... < 0, pf=None)
        """
        vs1 = [
            smt.FreshConst(v.sort(), prefix=v.decl().name().split("!")[0])
            for v in self.vs
        ]
        return Rule(
            vs1,
            hyp=smt.substitute(self.hyp, *zip(self.vs, vs1)),
            conc=smt.substitute(self.conc, *zip(self.vs, vs1)),
            pf=self.pf,
        )

    def to_expr(self) -> smt.ExprRef | smt.QuantifierRef:
        """Convert the rule to a theorem of form `forall vs, hyp => conc`.

        >>> x = smt.Real("x")
        >>> Rule([x], x > 0, x < 0).to_expr()
        ForAll(x..., Implies(x... > 0, x... < 0))
        """
        if len(self.vs) == 0:
            return smt.Implies(self.hyp, self.conc)
        else:
            return smt.ForAll(self.vs, smt.Implies(self.hyp, self.conc))


def rule_of_expr(pf_or_thm: smt.ExprRef | kd.kernel.Proof) -> Rule:
    """Unpack theorem of form `forall vs, body => head` into a Rule tuple

    >>> x = smt.Real("x")
    >>> rule_of_expr(smt.ForAll([x], smt.Implies(x**2 == x*x, x > 0)))
    Rule(vs=[X...], hyp=X...**2 == X...*X..., conc=X... > 0, pf=None)
    >>> rule_of_expr(x > 0)
    Rule(vs=[], hyp=True, conc=x > 0, pf=None)
    """
    if isinstance(pf_or_thm, smt.ExprRef):
        thm = pf_or_thm
        pf = None
    elif kd.kernel.is_proof(pf_or_thm):
        pf = pf_or_thm
        thm = pf.thm
    else:
        raise ValueError("Expected proof or theorem")
    if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
        vs, thm = utils.open_binder(thm)
    else:
        vs = []
    if smt.is_implies(thm):
        return Rule(vs, hyp=thm.arg(0), conc=thm.arg(1), pf=pf)
    else:
        assert isinstance(thm, smt.BoolRef)
        return Rule(vs, hyp=smt.BoolVal(True), conc=thm, pf=pf)


def backward_rule(
    r: Rule, tgt: smt.BoolRef
) -> Optional[tuple[dict[smt.ExprRef, smt.ExprRef], smt.BoolRef]]:
    """
    Apply a rule to a target term.
    """
    subst = kd.utils.pmatch(r.vs, r.conc, tgt)
    if subst is not None:
        return subst, smt.substitute(r.hyp, *subst.items())
    else:
        return None


def forward_rule(r: Rule, tgt: smt.BoolRef):
    """
    Apply a rule to a target term.
    """
    subst = kd.utils.pmatch(r.vs, r.hyp, tgt)
    if subst is not None:
        return smt.substitute(r.conc, *subst.items())
    else:
        return None


def horn_trig(e: kd.kernel.Proof) -> kd.kernel.Proof:
    """
    Take a horn clause and add triggers to it for the head

    >>> x = smt.Int("x")
    >>> pf = kd.prove(smt.ForAll([x], x > 0, x >= 0))
    >>> pf2 = horn_trig(pf)
    >>> pf2
    |= ForAll(X!..., Implies(X!... > 0, X!... >= 0))
    >>> pf2.thm.pattern(0)
    Var(0) >= 0
    """
    rule = rule_of_expr(e)
    if rule.vs:
        return kd.kernel.rename_vars2(e, rule.vs, patterns=[rule.conc])
    else:
        raise Exception("No variables in horn clause", e)


def rw_trig(e: kd.kernel.Proof, rev=False) -> kd.kernel.Proof:
    """
    Take a rewrite rule and add triggers to it for the lhs or rhs

    >>> x = smt.Int("x")
    >>> pf = kd.prove(smt.ForAll([x], x + 1 == 1 + x))
    >>> pf2 = rw_trig(pf)
    >>> pf2
    |= ForAll(X!..., X!... + 1 == 1 + X!...)
    >>> pf2.thm.pattern(0)
    Var(0) + 1
    >>> rw_trig(pf,rev=True).thm.pattern(0)
    1 + Var(0)
    """
    rule = rewrite_of_expr(e)
    if rule.vs:
        if not rev:
            return kd.kernel.rename_vars2(e, rule.vs, patterns=[rule.lhs])
        else:
            return kd.kernel.rename_vars2(e, rule.vs, patterns=[rule.rhs])
    else:
        raise Exception("No variables in rewrite", e)


"""
def apply_horn(thm: smt.BoolRef, horn: smt.BoolRef) -> smt.BoolRef:
    pat = horn
    obl = []
    if smt.is_quantifier(pat) and pat.is_forall():
        pat = pat.body()
    while True:
        if smt.is_implies(pat):
            obl.append(pat.arg(0))
            pat = pat.arg(1)
        else:
            break
    return kd.utils.z3_match(thm, pat)


def horn_split(horn: smt.BoolRef) -> smt.BoolRef:
    body = []
    vs = []
    while True:
        if smt.is_quantifier(horn) and horn.is_forall():
            vs1, horn = open_binder(horn)
            vs.extend(vs1)
        if smt.is_implies(horn):
            body.append(horn.arg(0))
            horn = horn.arg(1)
        else:
            break
    head = horn
    return vs, body, head
"""


class Order(Enum):
    EQ = 0  # Equal
    GR = 1  # Greater
    NGE = 2  # Not Greater or Equal


def lpo(vs: list[smt.ExprRef], t1: smt.ExprRef, t2: smt.ExprRef) -> Order:
    """
    Lexicographic path ordering.
    Based on https://www21.in.tum.de/~nipkow/TRaAT/programs/termorders.ML
    TODO add ordering parameter.
    """

    def is_var(x):
        return any(x.eq(v) for v in vs)

    if is_var(t2):
        if t1.eq(t2):
            return Order.EQ
        elif utils.is_subterm(t2, t1):
            return Order.GR
        else:
            return Order.NGE
    elif is_var(t1):
        return Order.NGE
    elif smt.is_app(t1) and smt.is_app(t2):
        decl1, decl2 = t1.decl(), t2.decl()
        args1, args2 = t1.children(), t2.children()
        if all(lpo(vs, a, t2) == Order.NGE for a in args1):
            if decl1 == decl2:
                if all(lpo(vs, t1, a) == Order.GR for a in args2):
                    for a1, a2 in zip(args1, args2):
                        ord = lpo(vs, a1, a2)
                        if ord == Order.GR:
                            return Order.GR
                        elif ord == Order.NGE:
                            return Order.NGE
                    return Order.EQ
                else:
                    return Order.NGE
            elif (decl1.name(), decl1.get_id()) > (decl2.name(), decl2.get_id()):
                if all(lpo(vs, t1, a) == Order.GR for a in args2):
                    return Order.GR
                else:
                    return Order.NGE

            else:
                return Order.NGE
        else:
            return Order.GR
    else:
        raise Exception("Unexpected terms in lpo", t1, t2)


def kbo(vs: list[smt.ExprRef], t1: smt.ExprRef, t2: smt.ExprRef) -> Order:
    """
    Knuth Bendix Ordering, naive implementation.
    All weights are 1.
    Source: Term Rewriting and All That section 5.4.4
    """
    if t1.eq(t2):
        return Order.EQ

    def is_var(x):
        return any(x.eq(v) for v in vs)

    def vcount(t):
        todo = [t]
        vcount1 = {v: 0 for v in vs}
        while todo:
            t = todo.pop()
            if is_var(t):
                vcount1[t] += 1
            elif smt.is_app(t):
                todo.extend(t.children())
        return vcount1

    vcount1, vcount2 = vcount(t1), vcount(t2)
    if not all(vcount1[v] >= vcount2[v] for v in vs):
        return Order.NGE

    def weight(t):
        todo = [t]
        w = 0
        while todo:
            t = todo.pop()
            w += 1
            if smt.is_app(t):
                todo.extend(t.children())
        return w

    w1, w2 = weight(t1), weight(t2)
    if w1 > w2:
        return Order.GR
    elif w1 < w2:
        return Order.NGE
    else:
        if is_var(t2):  # KBO2a
            decl = t1.decl()
            if decl.arity() != 1:
                return Order.NGE
            while not t1.eq(t2):
                if t1.decl() != decl:
                    return Order.NGE
                else:
                    t1 = t1.arg(0)
            return Order.GR
        elif is_var(t1):
            return Order.NGE
        elif smt.is_app(t1) and smt.is_app(t2):
            decl1, decl2 = t1.decl(), t2.decl()
            if decl1 == decl2:  # KBO2c
                args1, args2 = t1.children(), t2.children()
                for a1, a2 in zip(args1, args2):
                    ord = kbo(vs, a1, a2)
                    if ord == Order.GR:
                        return Order.GR
                    elif ord == Order.NGE:
                        return Order.NGE
                raise Exception("Unexpected equality reached in kbo")
            elif (decl1.name(), decl1.get_id()) > (
                decl2.name(),
                decl2.get_id(),
            ):  # KBO2b
                return Order.GR
            else:
                return Order.NGE
        else:
            raise Exception("Unexpected terms in kbo", t1, t2)
