"""
Utilities for rewriting and simplification including pattern matching and unification.
"""

import kdrag.smt as smt
import kdrag as kd
from enum import Enum
from typing import NamedTuple, Optional
import kdrag.utils as utils


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


def unfold(e: smt.ExprRef, decls=None, trace=None) -> smt.ExprRef:
    """
    Do a single unfold sweep, unfolding definitions defined by `kd.define`.
    The optional trace parameter will record proof along the way.
    `decls` is an optional list of declarations to unfold. If None, all definitions are unfolded.

    >>> x = smt.Int("x")
    >>> f = kd.define("f", [x], x + 42)
    >>> trace = []
    >>> unfold(f(1), trace=trace)
    1 + 42
    >>> trace
    [|- f(1) == 1 + 42]
    """
    if smt.is_app(e):
        decl = e.decl()
        children = [unfold(c, decls=decls, trace=trace) for c in e.children()]
        defn = kd.kernel.defns.get(decl)
        if defn is not None and (decls is None or decl in decls):
            e1 = smt.substitute(defn.body, *zip(defn.args, children))
            e = e1
            if trace is not None:
                if isinstance(defn.ax.thm, smt.QuantifierRef):
                    trace.append((defn.ax(*children)))
                else:
                    trace.append(defn.ax)
            return e1
        else:
            return decl(*children)
    else:
        return e


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
        return smt.substitute(rule.rhs, *subst.items())
        if trace is not None:
            trace.append((rule, subst))
    return None


def rewrite(t: smt.ExprRef, rules: list[RewriteRule], trace=None) -> smt.ExprRef:
    """
    Sweep through term once performing rewrites.

    >>> x = smt.Real("x")
    >>> rule = RewriteRule([x], x**2, x*x)
    >>> rewrite((x**2)**2, [rule])
    x*x*x*x
    """
    if smt.is_app(t):
        t = t.decl()(*[rewrite(arg, rules) for arg in t.children()])  # rewrite children
        for rule in rules:
            res = rewrite1_rule(t, rule, trace=trace)
            if res is not None:
                t = res
    return t


class RewriteRuleException(Exception): ...


def rule_of_theorem(thm: smt.BoolRef | smt.QuantifierRef) -> RewriteRule:
    """
    Unpack theorem of form `forall vs, lhs = rhs` into a Rule tuple

    >>> x = smt.Real("x")
    >>> rule_of_theorem(smt.ForAll([x], x**2 == x*x))
    RewriteRule(vs=[X...], lhs=X...**2, rhs=X...*X...)
    """
    vs = []
    thm1 = thm  # to help out pyright
    while isinstance(thm1, smt.QuantifierRef):
        if thm1.is_forall():
            vs1, thm1 = utils.open_binder(thm1)
            vs.extend(vs1)
        else:
            raise RewriteRuleException("Not a universal quantifier", thm1)
    if not smt.is_eq(thm1):
        raise RewriteRuleException("Not an equation", thm)
    lhs, rhs = thm1.children()
    return RewriteRule(vs, lhs, rhs)


def decl_index(rules: list[RewriteRule]) -> dict[smt.FuncDeclRef, RewriteRule]:
    """Build a dictionary of rules indexed by their lhs head function declaration."""
    return {rule.lhs.decl(): rule for rule in rules}


def rewrite_star(t: smt.ExprRef, rules: list[RewriteRule], trace=None) -> smt.ExprRef:
    """
    Repeat rewrite until no more rewrites are possible.
    """
    while True:
        t1 = rewrite(t, rules, trace=trace)
        if t1.eq(t):
            return t1
        t = t1


class Rule(NamedTuple):
    vs: list[smt.ExprRef]
    hyp: smt.BoolRef
    conc: smt.BoolRef
    pf: Optional[kd.kernel.Proof] = None


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
