import kdrag as kd
from kdrag import QForAll, prove
from kdrag.smt import (
    Array,
    BoolSort,
    BoolVal,
    Bools,
    Consts,
    DeclareTypeVar,
    ForAll,
    If,
    Implies,
)


B = BoolSort()
p, q, r = Bools("p q r")

or_comm = prove(ForAll([p, q], p | q == q | p))
or_assoc = prove(ForAll([p, q, r], (p | q) | r == p | (q | r)))
or_true = prove(ForAll([p], p | BoolVal(True) == BoolVal(True)))
or_false = prove(ForAll([p], p | BoolVal(False) == p))

or_idem = prove(ForAll([p], p | p == p))
or_absorb = prove(ForAll([p, q], p | (p & q) == p))
or_distr = prove(ForAll([p, q, r], p | (q & r) == (p | q) & (p | r)))
or_compl = prove(ForAll([p], p | ~p == BoolVal(True)))


and_comm = prove(ForAll([p, q], p & q == q & p))
and_assoc = prove(ForAll([p, q, r], (p & q) & r == p & (q & r)))
and_true = prove(ForAll([p], p & BoolVal(True) == p))
and_false = prove(ForAll([p], p & BoolVal(False) == BoolVal(False)))
and_absorb = prove(ForAll([p, q], (p & (p | q)) == p))
and_compl = prove(ForAll([p], p & ~p == BoolVal(False)))

and_idem = prove(ForAll([p], p & p == p))


imp_true = prove(ForAll([p], Implies(BoolVal(True), p) == p))
imp_false = prove(ForAll([p], Implies(BoolVal(False), p) == BoolVal(True)))
imp_idem = prove(ForAll([p], Implies(p, p) == BoolVal(True)))
imp_refl = prove(ForAll([p], Implies(p, p)))
imp_trans = prove(QForAll([p, q, r], Implies(p, q), Implies(q, r), Implies(p, r)))


not_true = prove(~BoolVal(True) == BoolVal(False))
not_false = prove(~BoolVal(False) == BoolVal(True))
not_inv = prove(ForAll([p], ~~p == p))  # Double negation elimination
not_and = prove(ForAll([p, q], ~(p & q) == (~p | ~q)))  # De Morgan’s Law
not_or = prove(ForAll([p, q], ~(p | q) == (~p & ~q)))  # De Morgan’s Law

xor_neq = prove(ForAll([p, q], (p ^ q) == (p != q)))
xor_comm = prove(ForAll([p, q], p ^ q == q ^ p))
xor_assoc = prove(ForAll([p, q, r], (p ^ q) ^ r == p ^ (q ^ r)))
xor_idem = prove(ForAll([p], p ^ p == BoolVal(False)))
xor_true = prove(ForAll([p], p ^ BoolVal(True) == ~p))
xor_false = prove(ForAll([p], p ^ BoolVal(False) == p))


T = DeclareTypeVar("T")
a, b = Consts("a b", T)
if_true = prove(ForAll([a, b], If(True, a, b) == a))
if_false = prove(ForAll([a, b], If(False, a, b) == b))


rws = [
    or_true,
    or_false,
    or_idem,
    or_absorb,
    or_distr,
    or_compl,
    and_comm,
    and_assoc,
    and_true,
    and_false,
    and_absorb,
    and_compl,
    imp_true,
    imp_false,
    imp_idem,
    imp_refl,
    xor_idem,
    xor_true,
    xor_false,
    if_true,
    if_false,
]

P = Array("P", B, B)
choose = kd.notation.choose.define([P], If(P[True], BoolVal(True), BoolVal(False)))
