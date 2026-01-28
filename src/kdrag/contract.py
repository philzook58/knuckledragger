from dataclasses import dataclass
import kdrag.smt as smt
import kdrag as kd


@dataclass(frozen=True)
class Contract:
    f: smt.FuncDeclRef
    args: list[smt.ExprRef]
    pre: smt.BoolRef
    post: smt.BoolRef
    proof: kd.Proof


contracts: dict[smt.FuncDeclRef, Contract] = {}

"""
def add_contract(f: smt.FuncDeclRef, proof: kd.Proof):
    assert f not in contracts
    contracts[f] = proof
"""


def lemmas(e: smt.ExprRef) -> list[kd.Proof]:
    """
    Instantiate all contract lemmas found in
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
            decls.update(kd.utils.decls(e.body()))
        else:
            raise ValueError(f"Unexpected term type: {e}")
    res.extend(contracts[decl].proof for decl in decls if decl in contracts)
    return res


def contract(
    f: smt.FuncDeclRef, args: list[smt.ExprRef], pre, post, by=None, **kwargs
) -> kd.Proof:
    """
    Register the contract for function f: for all args, pre => post.

    >>> x = smt.Int("x")
    >>> foo = kd.define("foo4392", [x], x + 1)
    >>> c = contract(foo, [x], x > 0, foo(x) > 0, by=[foo.defn])
    >>> c
    |= ForAll(x, Implies(x > 0, foo4392(x) > 0))
    >>> c.thm.pattern(0)
    foo4392(Var(0))
    >>> prove(foo(5) > 0)
    |= foo4392(5) > 0
    >>> prove(foo(5) > 5)
    Traceback (most recent call last):
        ...
    LemmaError: ...
    """
    assert f not in contracts
    if by is None:
        by = lemmas(pre) + lemmas(post)
    else:
        by = by + lemmas(pre) + lemmas(post)
    pf = kd.prove(smt.ForAll(args, pre, post, patterns=[f(*args)]), by=by, **kwargs)
    contracts[f] = Contract(f, args, pre, post, pf)
    return pf


# def define(name, args, body, pre=None, post=None): ...


def prove(thm: smt.BoolRef, by=[], **kwargs) -> kd.Proof:
    by = by + [
        contracts[decl].proof for decl in kd.utils.decls(thm) if decl in contracts
    ]
    return kd.prove(thm, by=by, **kwargs)
