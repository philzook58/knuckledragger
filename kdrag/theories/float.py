"""
Theory of built in floating point and connection to the reals
"""

import kdrag as kd
import kdrag.smt as smt
import sys

F16 = smt.Float16()
F32 = smt.FloatSingle()
F64 = smt.FloatDouble()
F128 = smt.FloatQuadruple()

# https://www.why3.org/stdlib/ieee_float.html


def IsFinite(x: smt.FPRef) -> smt.BoolRef:
    return smt.Or(smt.fpIsNormal(x), smt.fpIsSubnormal(x), smt.fpIsZero(x))


def NoOverflow(m, x: smt.ArithRef, s):
    return IsFinite(smt.fpRealToFP(m, x, s))


zeroF_is_positive = kd.prove(smt.fpIsPositive(smt.fpZero(F32, False)))
zeroF_is_negative = kd.prove(smt.fpIsNegative(smt.fpZero(F32, True)))

RMSort = smt.RNE().sort()

# a real -> real extension of rounding
round = smt.Function("round32", RMSort, smt.RealSort(), smt.RealSort())
x, y = smt.Reals("x y")
m, m1, m2 = smt.Consts("m m1 m2", RMSort)
# Actually, let's just complete it to the identity function and use kd.define?
round_def = kd.axiom(
    kd.QForAll(
        [m, x],
        NoOverflow(m, x, F32),
        round(m, x) == smt.fpToReal(smt.fpRealToFP(m, x, F32)),
    )
)


pow2sb = smt.IntVal(16777216)
max_int = smt.IntVal(0xFFFF_FF00_0000_0000_0000_0000_0000_0000)
max_real = smt.RealVal(2 - 2**-23) * 2**127  # smt.RealVal(0xFFFFFE * 2**121)
z = smt.Const("z", F32)
max_real_thm = kd.prove(
    kd.QForAll([z], IsFinite(z), z <= smt.fpRealToFP(smt.RNE(), max_real, F32))
)
minfloat = kd.prove(
    kd.QForAll([z], IsFinite(z), z >= smt.fpRealToFP(smt.RNE(), -max_real, F32))
)

special_cases = kd.prove(
    smt.ForAll(
        [z],
        smt.Or(
            smt.fpIsNaN(z),
            smt.fpIsInf(z),
            smt.fpIsZero(z),
            smt.fpIsNormal(z),
            smt.fpIsSubnormal(z),
        ),
    )
)


def in_range(x):
    return smt.And(-max_real <= x, x <= max_real)


def is_finite(x: smt.FPRef):
    return in_range(smt.fpToReal(x))


def no_overflow(m, x):
    return in_range(round(m, x))


bounded_real_no_overflow = kd.prove(
    # kd.QForAll( # quantifier form doesn't pass?
    #    [m, x],
    smt.Implies(in_range(x), NoOverflow(m, x, F32))
    # )
)

bounded_no_overflow = kd.axiom(kd.QForAll([m, x], in_range(x), no_overflow(m, x)))
# round_monotonic shouldn't be an axiom if IsFinite(round). We need the axiom to extend rounding to be monotonic outside the range out floats.
round_monotonic = kd.axiom(kd.QForAll([x, y], x <= y, round(m, x) <= round(m, y)))
round_idem = kd.axiom(kd.QForAll([x, m1, m2], round(m1, round(m2, x)) == round(m2, x)))

round_to_real = kd.axiom(
    kd.QForAll([z, m], IsFinite(z), round(m, smt.fpToReal(z)) == smt.fpToReal(z))
)

round_down_le = kd.axiom(smt.ForAll([x], round(smt.RTN(), x) <= x))
round_up_ge = kd.axiom(smt.ForAll([x], round(smt.RTP(), x) >= x))
round_down_neg = kd.axiom(smt.ForAll([x], round(smt.RTN(), -x) == -round(smt.RTP(), x)))
round_up_neg = kd.axiom(smt.ForAll([x], round(smt.RTP(), -x) == -round(smt.RTN(), x)))


"""
round_idem_finite = kd.prove(
    kd.QForAll(
        [x, m1, m2],
        NoOverflow(m2, x, F32),
        round(m1, round(m2, x)) == round(m2, x),
    ),
    by=round_def,
)
"""


max64 = smt.RealVal(sys.float_info.max)
z = smt.Const("z", F64)
max_real_thm = kd.prove(
    kd.QForAll([z], IsFinite(z), z <= smt.fpRealToFP(smt.RNE(), max64, F64))
)
min_float64 = kd.prove(
    kd.QForAll([z], IsFinite(z), z >= smt.fpRealToFP(smt.RNE(), -max64, F64))
)
"""
>>> assert True
"""


"""
Single
  lemma round_bound_ne :
    forall x:real [round RNE x].
      no_overflow RNE x ->
        x - 0x1p-24 * Abs.abs(x) - 0x1p-150 <= round RNE x <= x + 0x1p-24 * Abs.abs(x) + 0x1p-150

  lemma round_bound :
    forall m:mode, x:real [round m x].
      no_overflow m x ->
      x - 0x1p-23 * Abs.abs(x) - 0x1p-149 <= round m x <= x + 0x1p-23 * Abs.abs(x) + 0x1p-149

Double
  lemma round_bound_ne :
    forall x:real [round RNE x].
      no_overflow RNE x ->
        x - 0x1p-53 * Abs.abs(x) - 0x1p-1075 <= round RNE x <= x + 0x1p-53 * Abs.abs(x) + 0x1p-1075

  lemma round_bound :
    forall m:mode, x:real [round m x].
      no_overflow m x ->
      x - 0x1p-52 * Abs.abs(x) - 0x1p-1074 <= round m x <= x + 0x1p-52 * Abs.abs(x) + 0x1p-1074
"""


"""


"""


"""
get_default_rounding_mode (ctx=None)
set_default_rounding_mode (rm, ctx=None)
get_default_fp_sort (ctx=None)
set_default_fp_sort (ebits, sbits, ctx=None)
Float16 (ctx=None)
FloatHalf (ctx=None)
Float32 (ctx=None)
FloatSingle (ctx=None)
Float64 (ctx=None)
FloatDouble (ctx=None)
Float128 (ctx=None)
FloatQuadruple (ctx=None)
is_fp_sort (s)
is_fprm_sort (s)
RoundNearestTiesToEven (ctx=None)
RNE (ctx=None)
RoundNearestTiesToAway (ctx=None)
RNA (ctx=None)
RoundTowardPositive (ctx=None)
RTP (ctx=None)
RoundTowardNegative (ctx=None)
RTN (ctx=None)
RoundTowardZero (ctx=None)
RTZ (ctx=None)
is_fprm (a)
is_fprm_value (a)
is_fp (a)
is_fp_value (a)
FPSort (ebits, sbits, ctx=None)
fpNaN (s)
fpPlusInfinity (s)
fpMinusInfinity (s)
fpInfinity (s, negative)
fpPlusZero (s)
fpMinusZero (s)
fpZero (s, negative)
FPVal (sig, exp=None, fps=None, ctx=None)
FP (name, fpsort, ctx=None)
FPs (names, fpsort, ctx=None)
fpAbs (a, ctx=None)
fpNeg (a, ctx=None)
fpAdd (rm, a, b, ctx=None)
fpSub (rm, a, b, ctx=None)
fpMul (rm, a, b, ctx=None)
fpDiv (rm, a, b, ctx=None)
fpRem (a, b, ctx=None)
fpMin (a, b, ctx=None)
fpMax (a, b, ctx=None)
fpFMA (rm, a, b, c, ctx=None)
fpSqrt (rm, a, ctx=None)
fpRoundToIntegral (rm, a, ctx=None)
fpIsNaN (a, ctx=None)
fpIsInf (a, ctx=None)
fpIsZero (a, ctx=None)
fpIsNormal (a, ctx=None)
fpIsSubnormal (a, ctx=None)
fpIsNegative (a, ctx=None)
fpIsPositive (a, ctx=None)
fpLT (a, b, ctx=None)
fpLEQ (a, b, ctx=None)
fpGT (a, b, ctx=None)
fpGEQ (a, b, ctx=None)
fpEQ (a, b, ctx=None)
fpNEQ (a, b, ctx=None)
fpFP (sgn, exp, sig, ctx=None)
fpToFP (a1, a2=None, a3=None, ctx=None)
fpBVToFP (v, sort, ctx=None)
fpFPToFP (rm, v, sort, ctx=None)
fpRealToFP (rm, v, sort, ctx=None)
 
fpSignedToFP (rm, v, sort, ctx=None)
fpUnsignedToFP (rm, v, sort, ctx=None)
fpToFPUnsigned (rm, x, s, ctx=None)
fpToSBV (rm, x, s, ctx=None)
fpToUBV (rm, x, s, ctx=None)
fpToReal (x, ctx=None)
fpToIEEEBV (x, ctx=None)
"""
