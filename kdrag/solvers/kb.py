"""
Knuth Bendix completion.

When it succeeds, completion converts equations or non confluent rewriting systems into confluent ones.
The resulting system of rewrite rules is a decision procedure for the equivalence of terms.

It can be seen as a form of equational theorem proving, especially in it's unfailing form.

For more see

- Term Rewriting and All That (TRaaT) by Franz Baader and Tobias Nipkow
- https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion

"""

import kdrag.smt as smt
import kdrag.rewrite as rw
import sys


def all_pairs(rules):
    """
    Find all the ways the left hand side of two rules can overlap.
    Return a derived equation

    >>> a,b,c,d = smt.Reals("a b c d")
    >>> all_pairs([rw.RewriteRule(vs=[], lhs=x, rhs=y) for x,y in [(a,b), (b,c), (a,c), (a,d)]])
    [b == b, b == c, b == d, c == c, c == b, c == c, c == d, d == b, d == c, d == d]
    """
    # TODO. I'm not treating encompassment correctly
    res = []
    for rule1 in rules:
        for rule2 in rules:
            # we're double counting when rule1 = rule2 but whatever
            if any(v1.eq(v2) for v1 in rule1.vs for v2 in rule2.vs):
                rule2 = rule2.freshen()
            vs = rule1.vs + rule2.vs
            for t, subst in rw.all_narrow(vs, rule1.lhs, rule2.lhs, rule2.rhs):
                apply_rule1 = smt.substitute(rule1.rhs, *subst.items())
                apply_rule2 = smt.substitute(t, *subst.items())
                vs1 = list(set(vs) - set(subst.keys()))
                if len(vs1) == 0:
                    res.append(apply_rule1 == apply_rule2)
                else:
                    res.append(
                        smt.ForAll(vs1, apply_rule1 == apply_rule2)
                    )  # new derived equation
    return res


def orient(eq: smt.BoolRef | smt.QuantifierRef, order=rw.kbo) -> rw.RewriteRule:
    """
    Orient an equation into a rewrite rule.

    >>> x,y,z = smt.Reals("x y z")
    >>> orient(smt.ForAll([x], -(-x) == x))
    RewriteRule(vs=[X!...], lhs=--X!..., rhs=X!..., pf=None)
    >>> orient(smt.ForAll([x], x == -(-x)))
    RewriteRule(vs=[X!...], lhs=--X!..., rhs=X!..., pf=None)
    >>> orient(smt.ForAll([x,y,z], x + z == x + y + z + x + y))
    RewriteRule(vs=[X!...], lhs=X!... + Y!... + Z!... + X!... + Y!..., rhs=X!... + Z!..., pf=None)
    """
    r = rw.rewrite_of_expr(eq)
    if order(r.vs, r.lhs, r.rhs) == rw.Order.GR:
        return r
    elif order(r.vs, r.rhs, r.lhs) == rw.Order.GR:
        return r._replace(lhs=r.rhs, rhs=r.lhs)
    else:
        raise Exception("Cannot orient: " + str(eq))


def simplify(
    t: smt.BoolRef | smt.QuantifierRef, rules: list[rw.RewriteRule]
) -> smt.BoolRef | smt.QuantifierRef:
    """
    Simplify an equation using a set of rewrite rules.

    >>> x = smt.Real("x")
    >>> simplify(smt.ForAll([x], -(-(-(-(-x)))) == -x), [rw.rewrite_of_expr(smt.ForAll([x], -(-x) == x))])
    ForAll(X!..., -X!... == -X!...)
    """
    r = rw.rewrite_of_expr(t)
    lhs = rw.rewrite(r.lhs, rules)
    rhs = rw.rewrite(r.rhs, rules)
    return r._replace(lhs=lhs, rhs=rhs).to_expr()


def is_trivial(t: smt.BoolRef | smt.QuantifierRef) -> bool:
    """
    See if equation is of form `s = s

    >>> x = smt.Real("x")
    >>> assert is_trivial(x == x)
    >>> assert not is_trivial(x == -(-x))
    """
    r = rw.rewrite_of_expr(t)
    return r.lhs.eq(r.rhs)


def basic(E, order=rw.kbo):
    """
    Basic Knuth Bendix completion algorithm.

     TRaaT 7.1.1 Central Groupoid example
    >>> import kdrag as kd
    >>> T = smt.DeclareSort("CentralGroupoid")
    >>> x,y,z = smt.Consts("x y z", T)
    >>> mul = smt.Function("mul", T, T, T)
    >>> kd.notation.mul.register(T, mul)
    >>> E = [smt.ForAll([x,y,z], (x * y) * (y * z) == y)]
    >>> assert len(basic(E)) == 3
    """
    R = []
    for eq in E:
        R.append(orient(eq, order=order))
    i = 0
    done = False
    while not done:
        done = True
        for eq in all_pairs(R):
            eq1 = simplify(eq, R)
            if not is_trivial(eq1):
                R.append(orient(eq1))
                done = False
        i += 1
    return R


def huet(
    E: list[smt.BoolRef | smt.QuantifierRef], order=rw.kbo
) -> list[rw.RewriteRule]:
    """
    Huet completion is a particular strategy.
    """
    E = E.copy()
    R = []
    while True:
        while E:
            eq = E.pop()
            eq = simplify(eq, R)
            if is_trivial(eq):
                continue
            r = orient(eq, order=order)
            Rnew = [r]
            for r1 in R:
                lhs1 = rw.rewrite(r1.lhs, [r])
                if lhs1.eq(r1.lhs):
                    rhs1 = rw.rewrite(r1.rhs, R + [r])
                    Rnew.append(r1._replace(rhs=rhs1))
                else:
                    E.append(r1._replace(lhs=lhs1).to_expr())
            R = Rnew
        for eq in all_pairs(R):
            # by marking rules, we can prune the critical pair search, but I haven't done that
            # This is something like a semi-naive or given clause optimization
            # Always smash against at least 1 fresh new thing (rule in this case).
            # It might help a lot. Perfomance benchmarking suggests simplify is the bottleneck
            eq1 = simplify(eq, R)
            if not is_trivial(eq1):
                E.append(eq1)
                # break
        if len(E) == 0:
            return R


def huet_smt2_file(sexp_filename: str) -> list[rw.RewriteRule]:
    constrs = smt.parse_smt2_file(sexp_filename)
    return huet(list(constrs))


if __name__ == "__main__":
    for r in huet_smt2_file(sys.argv[1]):
        print(r.to_expr().sexpr())
