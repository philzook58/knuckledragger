import functools
import kdrag.smt as smt
import kdrag as kd
import kdrag.theories.set as set_


@functools.cache
def Filter(T: smt.SortRef):
    """
    A sort generic filter over sets of type T.

    >>> Filter(smt.RealSort())
    Filter_Real
    """
    dt = kd.Struct(f"Filter_{T}", ("sets", smt.SetSort(smt.SetSort(T))))
    A, B = smt.Consts("A B", smt.SetSort(T))
    F = smt.Const("F", dt)
    kd.notation.call.register(dt, lambda F, A: dt.sets(F)[A])
    kd.notation.wf.define(
        [F],
        smt.And(
            F(smt.FullSet(T)),
            smt.ForAll([A, B], F(A), A <= B, F(B)),
            smt.ForAll([A, B], F(A), F(B), F(A & B)),
        ),
    )
    return dt


class FilterMod:
    """
    A module encapsulating filter theory over sets of type T.

    >>> FilterMod(smt.RealSort()).filter_full
    |= ForAll(F, Implies(wf(F), sets(F)[K(Real, True)]))
    """

    def __init__(self, T: smt.SortRef):
        self.T = T
        self.S = Filter(T)
        F = smt.Const("F", self.S)
        set_.Set(T)
        A, B = smt.Consts("A B", smt.SetSort(T))
        self.filter_full = kd.prove(kd.QForAll([F], F(smt.FullSet(T))), unfold=1)
        self.filter_mono = kd.prove(
            kd.QForAll([F], smt.ForAll([A, B], F(A), A <= B, F(B))), unfold=1
        )
        self.filter_inter = kd.prove(
            kd.QForAll([F], smt.ForAll([A, B], F(A), F(B), F(A & B))), unfold=1
        )

    # @functools,cached_property
