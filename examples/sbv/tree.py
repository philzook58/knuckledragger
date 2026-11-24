"""Binary tree mirroring, size, and in-order traversal.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/Tree.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/Tree.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/tree.py
"""

from kdrag import Inductive, Tail, Theorem, define, prove
from kdrag.datatype import define_primrec
from kdrag.smt import (
    And,
    Const,
    Consts,
    DeclareSort,
    Empty,
    ForAll,
    Function,
    If,
    IntSort,
    IntVal,
    SeqSort,
)
from kdrag.tactics import ProofState

Element = DeclareSort("SBV.Tree.Element")
List = SeqSort(Element)
Tree = Inductive("SBV.Tree.Tree")
Tree.declare("Leaf")
Tree.declare("Node", ("left", Tree), ("value", Element), ("right", Tree))
Tree = Tree.create()
t, left, right = Consts("t left right", Tree)
x = Const("x", Element)
nil = Empty(List)

# Constructor handlers receive recursive results for the subtree fields.
mirror = define_primrec(
    "SBV.Tree.mirror",
    t,
    Tree,
    Leaf=lambda: Tree.Leaf,
    Node=lambda left, x, right: Tree.Node(right, x, left),
)
flatten = define_primrec(
    "SBV.Tree.flatten",
    t,
    List,
    Leaf=lambda: nil,
    Node=lambda left, x, right: left + [x] + right,
)
tree_size = define_primrec(
    "SBV.Tree.tree_size",
    t,
    IntSort(),
    Leaf=lambda: IntVal(0),
    Node=lambda left, x, right: 1 + left + right,
)


@Theorem(ForAll(t, tree_size(t) >= 0))
def tree_size_nonneg(pf: ProofState):
    t = pf.fix()
    pf.induct(t)
    pf.auto(by=[tree_size.defn])
    left, x, right = pf.fixes()
    pf.auto(by=[tree_size.defn])


tree_size_smaller = prove(
    ForAll(
        [left, x, right],
        And(
            tree_size(left) < tree_size(Tree.Node(left, x, right)),
            tree_size(right) < tree_size(Tree.Node(left, x, right)),
        ),
    ),
    by=[tree_size.defn, tree_size_nonneg],
)


@Theorem(ForAll(t, mirror(mirror(t)) == t))
def mirror_involution(pf: ProofState):
    # Structural induction supplies both subtree IHs, without a size measure.
    t = pf.fix()
    pf.induct(t)
    pf.auto(by=[mirror.defn])
    left, x, right = pf.fixes()
    pf.auto(by=[mirror.defn])


@Theorem(ForAll(t, tree_size(mirror(t)) == tree_size(t)))
def size_mirror(pf: ProofState):
    t = pf.fix()
    pf.induct(t)
    pf.auto(by=[mirror.defn, tree_size.defn])
    left, x, right = pf.fixes()
    pf.auto(by=[mirror.defn, tree_size.defn])


# SBV imports reverse/append from its Lists example. Prove that helper here
# over finite SMT sequences, with the same reverse equation as RevAcc.
xs, ys = Consts("xs ys", List)
reverse = Function("SBV.Tree.reverse", List, List)
reverse = define(
    "SBV.Tree.reverse",
    xs,
    If(xs == nil, nil, reverse(Tail(xs)) + [xs[0]]),
)


@Theorem(ForAll([xs, ys], reverse(xs + ys) == reverse(ys) + reverse(xs)))
def reverse_append(pf: ProofState):
    xs, ys = pf.fixes()
    pf.induct(xs)
    pf.auto(by=[reverse.defn])
    x, xs = pf.fixes()
    pf.auto(by=[reverse.defn])


@Theorem(ForAll(t, flatten(mirror(t)) == reverse(flatten(t))))
def flatten_mirror(pf: ProofState):
    t = pf.fix()
    pf.induct(t)
    pf.auto(by=[mirror.defn, flatten.defn, reverse.defn])
    left, x, right = pf.fixes()
    pf.auto(by=[mirror.defn, flatten.defn, reverse_append, reverse.defn])


if __name__ == "__main__":
    print(mirror_involution)
    print(size_mirror)
    print(flatten_mirror)
