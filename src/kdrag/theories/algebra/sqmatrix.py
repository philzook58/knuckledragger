import kdrag as kd
from kdrag import QForAll, axiom, define, prove
from kdrag.smt import (
    BoolSort,
    Const,
    Consts,
    DeclareSort,
    ForAll,
    Function,
    RealSort,
    Reals,
)

"""
Square matrices of a single dimension
"""

SqMat = DeclareSort("SqMat")
A, B, C = Consts("A B C", SqMat)

add = Function("add", SqMat, SqMat, SqMat)
kd.notation.add.register(SqMat, add)
add_assoc = axiom(ForAll([A, B, C], A + (B + C) == (A + B) + C))
add_comm = axiom(ForAll([A, B], A + B == B + A))

zero = Const("zero", SqMat)
add_zero = axiom(ForAll([A], A + zero == A))
zero_add = prove(ForAll([A], zero + A == A), by=[add_comm, add_zero])


smul = Function("smul", RealSort(), SqMat, SqMat)
kd.notation.mul.register(SqMat, lambda x, y: smul(y, x))
kd.notation.rmul.register(SqMat, lambda x, y: smul(y, x))
r, s = Reals("r s")
smul_zero = axiom(ForAll([A], 0 * A == zero))  # Is this a lemma?
smul_assoc = axiom(ForAll([A, r, s], smul(s, smul(r, A)) == smul(s * r, A)))
smul_comm = prove(
    ForAll([A, s, r], smul(r, smul(s, A)) == smul(s, smul(r, A))), by=[smul_assoc]
)


matmul = Function("mul", SqMat, SqMat, SqMat)
kd.notation.matmul.register(SqMat, matmul)
mul_assoc = axiom(ForAll([A, B, C], A @ (B @ C) == (A @ B) @ C))

mul_left_dist = axiom(ForAll([A, B, C], A @ (B + C) == A @ B + A @ C))
mul_right_dist = axiom(ForAll([A, B, C], (A + B) @ C == A @ C + B @ C))

I = Const("I", SqMat)
id_mul = axiom(ForAll([A], I @ A == A))
mul_id = axiom(ForAll([A], A @ I == A))

trans = Function("trans", SqMat, SqMat)
trans_idem = axiom(ForAll([A], trans(trans(A)) == A))


inv = Function("inv", SqMat, SqMat)
is_inv = Function("is_inv", SqMat, BoolSort())

inv_is_inv = axiom(ForAll([A], is_inv(A) == is_inv(inv(A))))

inv_left = axiom(QForAll([A], is_inv(A), inv(A) @ A == I))
inv_right = axiom(QForAll([A], is_inv(A), A @ inv(A) == I))

# inv_unique

is_symm = define("is_symm", [A], trans(A) == A)
is_orth = define("is_orth", [A], A @ trans(A) == I)

is_idem = define(
    "is_idem", [A], A @ A == A
)  # projection matrices https://en.wikipedia.org/wiki/Projection_(linear_algebra)
# orth_trans_inv = kd.prove(smt.QForAll([A], is_orth(A), inv(A) == trans(A)))


is_diag = Function("is_diag", SqMat, BoolSort())

trace = Function("trace", SqMat, RealSort())
