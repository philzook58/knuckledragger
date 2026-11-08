import functools
import kdrag.smt as smt
from kdrag.smt import And, Const, Consts, ForAll, FullSet, RealSort, SetSort  # noqa: F401
import kdrag as kd
from kdrag import QForAll, Struct, prove
import kdrag.theories.set as set_


@functools.cache
def Filter(T: smt.SortRef):
    """
    A sort generic filter over sets of type T.

    >>> Filter(RealSort())
    Filter_Real
    """
    dt = Struct(f"Filter_{T}", ("sets", SetSort(SetSort(T))))
    A, B = Consts("A B", SetSort(T))
    F = Const("F", dt)
    kd.notation.call.register(dt, lambda F, A: dt.sets(F)[A])
    kd.notation.wf.define(
        [F],
        And(
            F(FullSet(T)),
            ForAll([A, B], F(A), A <= B, F(B)),
            ForAll([A, B], F(A), F(B), F(A & B)),
        ),
    )
    return dt


class FilterMod:
    """
    A module encapsulating filter theory over sets of type T.

    >>> FilterMod(RealSort()).filter_full
    |= ForAll(F, Implies(Filter_Real.wf(F), sets(F)[K(Real, True)]))
    """

    def __init__(self, T: smt.SortRef):
        self.T = T
        self.S = Filter(T)
        F = Const("F", self.S)
        set_.Set(T)
        A, B = Consts("A B", SetSort(T))
        self.filter_full = prove(QForAll([F], F(FullSet(T))), unfold=1)
        self.filter_mono = prove(
            QForAll([F], ForAll([A, B], F(A), A <= B, F(B))), unfold=1
        )
        self.filter_inter = prove(
            QForAll([F], ForAll([A, B], F(A), F(B), F(A & B))), unfold=1
        )

    # @functools,cached_property
