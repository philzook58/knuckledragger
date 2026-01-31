"""

Contracts are a database of lemmas associated with a function symbol.
They are usually used to specify intended pre and postconditions for functions as an abstraction over their definition.
This can also be though of as a subtyping refinement.

There is a registry which can be queried.

This registry is not trusted code.

"""

from dataclasses import dataclass
import kdrag.smt as smt
import kdrag as kd


@dataclass(frozen=True)
class Contract:
    f: smt.FuncDeclRef
    args: list[smt.ExprRef]
    pre: smt.BoolRef
    post: smt.BoolRef
    proof: kd.kernel.Proof


contracts: dict[smt.FuncDeclRef, Contract] = {}


def lemmas(e: smt.ExprRef, into_binders=True) -> list[kd.kernel.Proof]:
    """
    Instantiate all contract lemmas found in a pexression.
    This sweeps the expression and instantiates the contract lemma with the arguments to the function.
    Once it goes under binders, this becomes more difficult, so it returns the quantified form of the lemmas
    """
    res = []
    seen: set[int] = set([e.get_id()])
    todo = [e]
    decls = set()
    while todo:
        e = todo.pop()
        if smt.is_app(e):
            f = e.decl()
            children = e.children()
            if f in contracts:
                # we know how this should be instantiated
                res.append(contracts[f].proof(*children))
            for c in children:
                idx = c.get_id()
                if idx not in seen:
                    seen.add(idx)
                    todo.append(c)
        elif isinstance(e, smt.QuantifierRef):
            # There may be variables inside here. Fallback to just giving z3
            if into_binders:
                decls.update(kd.utils.decls(e.body()))
        else:
            raise ValueError(f"Unexpected term type: {e}")
    res.extend(contracts[decl].proof for decl in decls if decl in contracts)
    return res


def contract(
    f: smt.FuncDeclRef, args: list[smt.ExprRef], pre, post, by=None, **kwargs
) -> kd.kernel.Proof:
    """
    Register the contract for function f: for all args, pre => post.

    >>> x = smt.Int("x")
    >>> foo = kd.define("foo4392", [x], x + 1)
    >>> c = contract(foo, [x], x > 0, foo(x) > 0, by=[foo.defn])
    >>> c
    |= ForAll(x, Implies(x > 0, foo4392(x) > 0))
    >>> c.thm.pattern(0)
    foo4392(Var(0))
    >>> kd.prove(foo(5) > 0, contracts=True)
    |= foo4392(5) > 0
    >>> kd.prove(foo(5) > 5, contracts=True)
    Traceback (most recent call last):
        ...
    LemmaError: ...
    """
    assert f not in contracts
    if by is None:
        by = []
    thm = smt.ForAll(args, smt.Implies(pre, post), patterns=[f(*args)])
    by = by + lemmas(thm)
    pf = kd.kernel.prove(thm, by=by, **kwargs)  # Do we want kd.tactics.prove here?
    contracts[f] = Contract(f, args, pre, post, pf)
    return pf


# Special define?
