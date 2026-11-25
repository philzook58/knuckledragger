"""A focused proof that clamping gives a nearest point in a closed interval.

Run with `python examples/with_proof_focus.py`.
"""

from kdrag import Theorem
from kdrag.smt import Abs, And, ForAll, If, Reals

lo, hi, x, z = Reals("lo hi x z")


def clamp(x, lo, hi):
    return If(x < lo, lo, If(hi < x, hi, x))


@Theorem(
    ForAll(
        [x, lo, hi],
        lo <= hi,
        And(
            lo <= clamp(x, lo, hi),
            clamp(x, lo, hi) <= hi,
            ForAll(z, lo <= z, z <= hi, Abs(x - clamp(x, lo, hi)) <= Abs(x - z)),
        ),
    )
)
def clamp_is_nearest(l):
    x, lo, hi = l.fixes()
    l.intro()
    nearest = clamp(x, lo, hi)
    bounds = l.have(And(lo <= nearest, nearest <= hi))
    with l:
        l.auto()

    l.andE(bounds)
    l.split()
    l.assumption()
    l.assumption()
    z = l.fix()
    l.intros()
    l.cases(x < lo)
    with l:
        l.case(x < lo)
        at_lower_endpoint = l.have(nearest == lo, by=[])
        l.have(x < z, by=[])
        l.rw(at_lower_endpoint)
        l.auto()

    with l:
        l.case(lo <= x)
        l.cases(hi < x)
        with l:
            l.case(hi < x)
            at_upper_endpoint = l.have(nearest == hi, by=[])
            l.have(z < x, by=[])
            l.rw(at_upper_endpoint)
            l.auto()
        with l:
            l.case(x <= hi)
            unchanged = l.have(nearest == x, by=[])
            l.rw(unchanged)
            l.auto()


if __name__ == "__main__":
    print(clamp_is_nearest)
