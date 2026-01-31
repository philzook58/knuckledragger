# Imp: Simple Imperative Programs (partial translation from Imp.v)
# Note: Using Int for arithmetic for now (Nat subtraction isn't in the library yet).

import kdrag as kd
import kdrag.smt as smt
import kdrag.rewrite as kdrw
import lark

# --------------------------------------------------------------------
# Arithmetic and Boolean Expressions

AExp = kd.inductive(
    "inductive AExp where "
    "| ANum : Int -> AExp "
    "| APlus : AExp -> AExp -> AExp "
    "| AMinus : AExp -> AExp -> AExp "
    "| AMult : AExp -> AExp -> AExp"
)

BExp = kd.inductive(
    "inductive BExp where "
    "| BTrue : BExp "
    "| BFalse : BExp "
    "| BEq : AExp -> AExp -> BExp "
    "| BNeq : AExp -> AExp -> BExp "
    "| BLe : AExp -> AExp -> BExp "
    "| BGt : AExp -> AExp -> BExp "
    "| BNot : BExp -> BExp "
    "| BAnd : BExp -> BExp -> BExp"
)

aeval = kd.ldefine(
    "def aeval (a : AExp) : Int := "
    "match a with "
    "| AExp.ANum n => n "
    "| AExp.APlus a1 a2 => aeval a1 + aeval a2 "
    "| AExp.AMinus a1 a2 => aeval a1 - aeval a2 "
    "| AExp.AMult a1 a2 => aeval a1 * aeval a2"
)

beval = kd.ldefine(
    "def beval (b : BExp) : Bool := "
    "match b with "
    "| BExp.BTrue => True "
    "| BExp.BFalse => False "
    "| BExp.BEq a1 a2 => aeval a1 = aeval a2 "
    "| BExp.BNeq a1 a2 => aeval a1 != aeval a2 "
    "| BExp.BLe a1 a2 => aeval a1 <= aeval a2 "
    "| BExp.BGt a1 a2 => aeval a1 > aeval a2 "
    "| BExp.BNot b1 => beval b1 = False "
    "| BExp.BAnd b1 b2 => beval b1 /\\ beval b2"
)


@kd.Theorem("aeval (AExp.APlus (AExp.ANum 2) (AExp.ANum 2)) = 4")
def test_aeval1(pf):
    pf.auto(by=[aeval.defn])


optimize_0plus = kd.ldefine(
    "def optimize_0plus (a : AExp) : AExp := "
    "match a with "
    "| AExp.ANum n => AExp.ANum n "
    "| AExp.APlus (AExp.ANum 0) e2 => optimize_0plus e2 "
    "| AExp.APlus e1 e2 => AExp.APlus (optimize_0plus e1) (optimize_0plus e2) "
    "| AExp.AMinus e1 e2 => AExp.AMinus (optimize_0plus e1) (optimize_0plus e2) "
    "| AExp.AMult e1 e2 => AExp.AMult (optimize_0plus e1) (optimize_0plus e2)"
)


@kd.Theorem(
    "optimize_0plus "
    "(AExp.APlus (AExp.ANum 2) "
    "  (AExp.APlus (AExp.ANum 0) (AExp.APlus (AExp.ANum 0) (AExp.ANum 1)))) "
    "= AExp.APlus (AExp.ANum 2) (AExp.ANum 1)"
)
def test_optimize_0plus(pf):
    pf.auto(by=[optimize_0plus.defn])


# Common "by" bundles to reduce verbosity.
BY_AEVAL = [aeval.defn]
BY_BEVAL = [beval.defn, aeval.defn]


# --------------------------------------------------------------------
# Relational evaluation for arithmetic expressions.

AevalR = kd.inductive(
    "inductive AevalR where "
    "| AE_Num : Int -> AevalR "
    "| AE_Plus : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> AevalR "
    "| AE_Minus : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> AevalR "
    "| AE_Mult : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> AevalR"
)

aevalR_wf = kd.ldefine(
    "def aevalR_wf (ev : AevalR) (a : AExp) (n : Int) : Bool := "
    "match ev with "
    "| AevalR.AE_Num k => a = AExp.ANum k /\\ n = k "
    "| AevalR.AE_Plus a1 a2 n1 n2 ev1 ev2 => "
    "    a = AExp.APlus a1 a2 /\\ n = n1 + n2 /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2 "
    "| AevalR.AE_Minus a1 a2 n1 n2 ev1 ev2 => "
    "    a = AExp.AMinus a1 a2 /\\ n = n1 - n2 /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2 "
    "| AevalR.AE_Mult a1 a2 n1 n2 ev1 ev2 => "
    "    a = AExp.AMult a1 a2 /\\ n = n1 * n2 /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2"
)


@kd.Theorem(
    "exists (ev : AevalR), " "aevalR_wf ev (AExp.APlus (AExp.ANum 2) (AExp.ANum 2)) 4"
)
def aevalR_ex1(pf):
    pf.exists(
        AevalR.AE_Plus(
            AExp.ANum(2),
            AExp.ANum(2),
            2,
            2,
            AevalR.AE_Num(2),
            AevalR.AE_Num(2),
        )
    )
    pf.auto(by=[aevalR_wf.defn])


# --------------------------------------------------------------------
# Relational evaluation for boolean expressions.

BevalR = kd.inductive(
    "inductive BevalR where "
    "| BE_True : BevalR "
    "| BE_False : BevalR "
    "| BE_Eq : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> BevalR "
    "| BE_Neq : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> BevalR "
    "| BE_Le : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> BevalR "
    "| BE_Gt : AExp -> AExp -> Int -> Int -> AevalR -> AevalR -> BevalR "
    "| BE_Not : BExp -> BevalR -> BevalR "
    "| BE_And : BExp -> BExp -> BevalR -> BevalR -> BevalR"
)

bevalR_wf = kd.ldefine(
    "def bevalR_wf (ev : BevalR) (b : BExp) (v : Bool) : Bool := "
    "match ev with "
    "| BevalR.BE_True => b = BExp.BTrue /\\ v = True "
    "| BevalR.BE_False => b = BExp.BFalse /\\ v = False "
    "| BevalR.BE_Eq a1 a2 n1 n2 ev1 ev2 => "
    "    b = BExp.BEq a1 a2 /\\ v = (n1 = n2) /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2 "
    "| BevalR.BE_Neq a1 a2 n1 n2 ev1 ev2 => "
    "    b = BExp.BNeq a1 a2 /\\ v = (n1 != n2) /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2 "
    "| BevalR.BE_Le a1 a2 n1 n2 ev1 ev2 => "
    "    b = BExp.BLe a1 a2 /\\ v = (n1 <= n2) /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2 "
    "| BevalR.BE_Gt a1 a2 n1 n2 ev1 ev2 => "
    "    b = BExp.BGt a1 a2 /\\ v = (n1 > n2) /\\ "
    "    aevalR_wf ev1 a1 n1 /\\ aevalR_wf ev2 a2 n2 "
    "| BevalR.BE_Not b1 ev1 => b = BExp.BNot b1 /\\ v = (bevalR_wf ev1 b1 False) "
    "| BevalR.BE_And b1 b2 ev1 ev2 => "
    "    b = BExp.BAnd b1 b2 /\\ v = (bevalR_wf ev1 b1 True /\\ bevalR_wf ev2 b2 True)"
)


@kd.Theorem(
    "exists (ev : BevalR), "
    "bevalR_wf ev "
    "(BExp.BEq (AExp.ANum 2) (AExp.ANum 2)) True"
)
def bevalR_ex1(pf):
    pf.exists(
        BevalR.BE_Eq(
            AExp.ANum(2),
            AExp.ANum(2),
            2,
            2,
            AevalR.AE_Num(2),
            AevalR.AE_Num(2),
        )
    )
    pf.auto(by=[bevalR_wf.defn, aevalR_wf.defn])


# --------------------------------------------------------------------
# Expressions with variables and state.

Str = smt.StringSort()
State = smt.ArraySort(Str, smt.IntSort())

st = smt.Const("st", State)
vx = smt.String("x")
vv = smt.Int("v")

empty_state = kd.define("empty_state", [], smt.K(Str, smt.IntVal(0)))
lookup = kd.define("lookup", [st, vx], smt.Select(st, vx))
update = kd.define("update", [st, vx, vv], smt.Store(st, vx, vv))

A_W = "W"
A_X = "X"
A_Y = "Y"
A_Z = "Z"

AExpV = kd.inductive(
    "inductive AExpV where "
    "| ANum : Int -> AExpV "
    "| AVar : String -> AExpV "
    "| APlus : AExpV -> AExpV -> AExpV "
    "| AMinus : AExpV -> AExpV -> AExpV "
    "| AMult : AExpV -> AExpV -> AExpV"
)

BExpV = kd.inductive(
    "inductive BExpV where "
    "| BTrue : BExpV "
    "| BFalse : BExpV "
    "| BEq : AExpV -> AExpV -> BExpV "
    "| BNeq : AExpV -> AExpV -> BExpV "
    "| BLe : AExpV -> AExpV -> BExpV "
    "| BGt : AExpV -> AExpV -> BExpV "
    "| BNot : BExpV -> BExpV "
    "| BAnd : BExpV -> BExpV -> BExpV"
)

aeval_st = kd.ldefine(
    "def aeval_st (st : State) (a : AExpV) : Int := "
    "match a with "
    "| AExpV.ANum n => n "
    "| AExpV.AVar x => lookup st x "
    "| AExpV.APlus a1 a2 => aeval_st st a1 + aeval_st st a2 "
    "| AExpV.AMinus a1 a2 => aeval_st st a1 - aeval_st st a2 "
    "| AExpV.AMult a1 a2 => aeval_st st a1 * aeval_st st a2"
)

beval_st = kd.ldefine(
    "def beval_st (st : State) (b : BExpV) : Bool := "
    "match b with "
    "| BExpV.BTrue => True "
    "| BExpV.BFalse => False "
    "| BExpV.BEq a1 a2 => aeval_st st a1 = aeval_st st a2 "
    "| BExpV.BNeq a1 a2 => aeval_st st a1 != aeval_st st a2 "
    "| BExpV.BLe a1 a2 => aeval_st st a1 <= aeval_st st a2 "
    "| BExpV.BGt a1 a2 => aeval_st st a1 > aeval_st st a2 "
    "| BExpV.BNot b1 => beval_st st b1 = False "
    "| BExpV.BAnd b1 b2 => beval_st st b1 /\\ beval_st st b2"
)

BY_STATE = [
    aeval_st.defn,
    beval_st.defn,
    update.defn,
    lookup.defn,
    empty_state.defn,
]


@kd.Theorem(
    'aeval_st (update empty_state "X" 5) '
    '(AExpV.APlus (AExpV.AVar "X") (AExpV.ANum 2)) = 7'
)
def test_aeval_state(pf):
    pf.auto(by=BY_STATE)


@kd.Theorem(
    'beval_st (update empty_state "X" 5) '
    '(BExpV.BLe (AExpV.AVar "X") (AExpV.ANum 4)) = False'
)
def test_beval_state(pf):
    pf.auto(by=BY_STATE)


@kd.Theorem(
    'aeval_st (update empty_state "X" 5) '
    '(AExpV.APlus (AExpV.ANum 3) (AExpV.AMult (AExpV.AVar "X") (AExpV.ANum 2))) = 13'
)
def test_aeval_state2(pf):
    pf.auto(by=BY_STATE)


@kd.Theorem(
    'aeval_st (update (update empty_state "X" 5) "Y" 4) '
    '(AExpV.APlus (AExpV.AVar "Z") (AExpV.AMult (AExpV.AVar "X") (AExpV.AVar "Y"))) = 20'
)
def test_aeval_state3(pf):
    pf.auto(by=BY_STATE)


@kd.Theorem(
    'beval_st (update empty_state "X" 5) '
    '(BExpV.BAnd BExpV.BTrue (BExpV.BNot (BExpV.BLe (AExpV.AVar "X") (AExpV.ANum 4)))) = True'
)
def test_beval_state2(pf):
    pf.auto(by=BY_STATE)


# --------------------------------------------------------------------
# Commands and big-step evaluation.

Com = kd.inductive(
    "inductive Com where "
    "| CSkip : Com "
    "| CAss : String -> AExpV -> Com "
    "| CSeq : Com -> Com -> Com "
    "| CIf : BExpV -> Com -> Com -> Com "
    "| CWhile : BExpV -> Com -> Com"
)

Ceval = kd.inductive(
    "inductive Ceval where "
    "| CE_Skip : Ceval "
    "| CE_Ass : String -> AExpV -> Int -> Ceval "
    "| CE_Seq : State -> Ceval -> Ceval -> Ceval "
    "| CE_IfTrue : BExpV -> Com -> Com -> Ceval -> Ceval "
    "| CE_IfFalse : BExpV -> Com -> Com -> Ceval -> Ceval "
    "| CE_WhileFalse : BExpV -> Com -> Ceval "
    "| CE_WhileTrue : BExpV -> Com -> State -> Ceval -> Ceval -> Ceval"
)

ceval_wf = kd.ldefine(
    "def ceval_wf (ev : Ceval) (c : Com) (st st' : State) : Bool := "
    "match ev with "
    "| Ceval.CE_Skip => c = Com.CSkip /\\ st' = st "
    "| Ceval.CE_Ass x a n => "
    "    c = Com.CAss x a /\\ n = aeval_st st a /\\ st' = update st x n "
    "| Ceval.CE_Seq mid ev1 ev2 => "
    "    exists (c1 c2 : Com), c = Com.CSeq c1 c2 /\\ "
    "    ceval_wf ev1 c1 st mid /\\ ceval_wf ev2 c2 mid st' "
    "| Ceval.CE_IfTrue b c1 c2 ev1 => "
    "    c = Com.CIf b c1 c2 /\\ "
    "    beval_st st b = True /\\ ceval_wf ev1 c1 st st' "
    "| Ceval.CE_IfFalse b c1 c2 ev2 => "
    "    c = Com.CIf b c1 c2 /\\ "
    "    beval_st st b = False /\\ ceval_wf ev2 c2 st st' "
    "| Ceval.CE_WhileFalse b body => "
    "    c = Com.CWhile b body /\\ beval_st st b = False /\\ st' = st "
    "| Ceval.CE_WhileTrue b body mid ev1 ev2 => "
    "    c = Com.CWhile b body /\\ beval_st st b = True /\\ "
    "    ceval_wf ev1 body st mid /\\ ceval_wf ev2 c mid st'"
)

BY_CEVAL = [ceval_wf.defn] + BY_STATE


@kd.Theorem("ceval_wf Ceval.CE_Skip Com.CSkip empty_state empty_state")
def ceval_skip(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    'ceval_wf (Ceval.CE_Ass "X" (AExpV.ANum 5) 5) '
    '(Com.CAss "X" (AExpV.ANum 5)) '
    'empty_state (update empty_state "X" 5)'
)
def ceval_assign(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "ceval_wf "
    '(Ceval.CE_Seq (update empty_state "X" 5) '
    '(Ceval.CE_Ass "X" (AExpV.ANum 5) 5) '
    '(Ceval.CE_Ass "Y" (AExpV.ANum 7) 7)) '
    '(Com.CSeq (Com.CAss "X" (AExpV.ANum 5)) (Com.CAss "Y" (AExpV.ANum 7))) '
    'empty_state (update (update empty_state "X" 5) "Y" 7)'
)
def ceval_seq(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "ceval_wf "
    "(Ceval.CE_IfTrue "
    "(BExpV.BLe (AExpV.ANum 1) (AExpV.ANum 2)) "
    '(Com.CAss "X" (AExpV.ANum 1)) '
    '(Com.CAss "X" (AExpV.ANum 0)) '
    '(Ceval.CE_Ass "X" (AExpV.ANum 1) 1)) '
    "(Com.CIf (BExpV.BLe (AExpV.ANum 1) (AExpV.ANum 2)) "
    '(Com.CAss "X" (AExpV.ANum 1)) '
    '(Com.CAss "X" (AExpV.ANum 0))) '
    'empty_state (update empty_state "X" 1)'
)
def ceval_if_true(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "ceval_wf "
    "(Ceval.CE_WhileFalse "
    "(BExpV.BLe (AExpV.ANum 1) (AExpV.ANum 0)) "
    '(Com.CAss "X" (AExpV.ANum 1))) '
    "(Com.CWhile (BExpV.BLe (AExpV.ANum 1) (AExpV.ANum 0)) "
    '(Com.CAss "X" (AExpV.ANum 1))) '
    "empty_state empty_state"
)
def ceval_while_false(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "ceval_wf "
    "(Ceval.CE_WhileTrue "
    '(BExpV.BLe (AExpV.AVar "X") (AExpV.ANum 0)) '
    '(Com.CAss "X" (AExpV.APlus (AExpV.AVar "X") (AExpV.ANum 1))) '
    '(update empty_state "X" 1) '
    '(Ceval.CE_Ass "X" (AExpV.APlus (AExpV.AVar "X") (AExpV.ANum 1)) 1) '
    "(Ceval.CE_WhileFalse "
    '(BExpV.BLe (AExpV.AVar "X") (AExpV.ANum 0)) '
    '(Com.CAss "X" (AExpV.APlus (AExpV.AVar "X") (AExpV.ANum 1)))) ) '
    '(Com.CWhile (BExpV.BLe (AExpV.AVar "X") (AExpV.ANum 0)) '
    '(Com.CAss "X" (AExpV.APlus (AExpV.AVar "X") (AExpV.ANum 1)))) '
    'empty_state (update empty_state "X" 1)'
)
def ceval_while_true(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "ceval_wf "
    "(Ceval.CE_IfFalse "
    "(BExpV.BLe (AExpV.ANum 2) (AExpV.ANum 1)) "
    '(Com.CAss "X" (AExpV.ANum 1)) '
    '(Com.CAss "X" (AExpV.ANum 0)) '
    '(Ceval.CE_Ass "X" (AExpV.ANum 0) 0)) '
    "(Com.CIf (BExpV.BLe (AExpV.ANum 2) (AExpV.ANum 1)) "
    '(Com.CAss "X" (AExpV.ANum 1)) '
    '(Com.CAss "X" (AExpV.ANum 0))) '
    'empty_state (update empty_state "X" 0)'
)
def ceval_if_false(pf):
    pf.auto(by=BY_CEVAL)


# --------------------------------------------------------------------
# Tiny Imp parser (lark) to build Com ASTs.

IMP_GRAMMAR = r"""
start: com

?com: "skip"                        -> c_skip
    | NAME ":=" aexp                -> c_ass
    | com ";" com                   -> c_seq
    | "if" bexp "then" com "else" com "end" -> c_if
    | "while" bexp "do" com "end"   -> c_while
    | "(" com ")"

?aexp: term
    | aexp "+" term                 -> a_add
    | aexp "-" term                 -> a_sub
?term: factor
    | term "*" factor               -> a_mul
?factor: NUMBER                     -> a_num
    | NAME                          -> a_var
    | "(" aexp ")"

?bexp: bterm
    | bexp "&&" bterm               -> b_and
?bterm: "true"                      -> b_true
    | "false"                       -> b_false
    | "!" bterm                     -> b_not
    | "~" bterm                     -> b_not
    | aexp "=" aexp                 -> b_eq
    | aexp "==" aexp                -> b_eq
    | aexp "!=" aexp                -> b_neq
    | aexp "<>" aexp                -> b_neq
    | aexp "<=" aexp                -> b_le
    | aexp ">=" aexp                -> b_ge
    | aexp "<" aexp                 -> b_lt
    | aexp ">" aexp                 -> b_gt
    | "(" bexp ")"

%import common.CNAME -> NAME
%import common.NUMBER
%import common.WS
%ignore WS
"""


class ImpTransformer(lark.Transformer):
    def start(self, items):
        return items[0]

    def _s(self, tok):
        return smt.StringVal(str(tok))

    def a_num(self, items):
        return AExpV.ANum(int(items[0]))

    def a_var(self, items):
        return AExpV.AVar(self._s(items[0]))

    def a_add(self, items):
        return AExpV.APlus(items[0], items[1])

    def a_sub(self, items):
        return AExpV.AMinus(items[0], items[1])

    def a_mul(self, items):
        return AExpV.AMult(items[0], items[1])

    def b_true(self, _items):
        return BExpV.BTrue

    def b_false(self, _items):
        return BExpV.BFalse

    def b_not(self, items):
        return BExpV.BNot(items[0])

    def b_and(self, items):
        return BExpV.BAnd(items[0], items[1])

    def b_eq(self, items):
        return BExpV.BEq(items[0], items[1])

    def b_neq(self, items):
        return BExpV.BNeq(items[0], items[1])

    def b_le(self, items):
        return BExpV.BLe(items[0], items[1])

    def b_ge(self, items):
        return BExpV.BLe(items[1], items[0])

    def b_lt(self, items):
        return BExpV.BGt(items[1], items[0])

    def b_gt(self, items):
        return BExpV.BGt(items[0], items[1])

    def c_skip(self, _items):
        return Com.CSkip

    def c_ass(self, items):
        return Com.CAss(self._s(items[0]), items[1])

    def c_seq(self, items):
        return Com.CSeq(items[0], items[1])

    def c_if(self, items):
        return Com.CIf(items[0], items[1], items[2])

    def c_while(self, items):
        return Com.CWhile(items[0], items[1])


def parse_imp(src: str) -> smt.DatatypeRef:
    parser = lark.Lark(IMP_GRAMMAR, start="start", parser="lalr")
    tree = parser.parse(src)
    res = ImpTransformer().transform(tree)
    if isinstance(res, list) and len(res) == 1:
        res = res[0]
    return res


imp_demo = parse_imp("X := 1; Y := X + 2")
imp_demo_if = parse_imp("if X <= 1 then Y := 0 else Y := 1 end")
imp_demo_while = parse_imp("while X <> 0 do X := X - 1 end")
imp_demo_ge = parse_imp("if X >= 1 then skip else skip end")

c_example1 = parse_imp("X := 2; if X <= 1 then Y := 3 else Z := 4 end")
c_example2 = parse_imp("X := 0; Y := 1; Z := 2")


SX = smt.StringVal("X")
SY = smt.StringVal("Y")

_imp_seq_expected = Com.CSeq(
    Com.CAss(SX, AExpV.ANum(1)),
    Com.CAss(SY, AExpV.APlus(AExpV.AVar(SX), AExpV.ANum(2))),
)
assert smt.is_true(smt.simplify(imp_demo == _imp_seq_expected))

_imp_if_expected = Com.CIf(
    BExpV.BLe(AExpV.AVar(SX), AExpV.ANum(1)),
    Com.CAss(SY, AExpV.ANum(0)),
    Com.CAss(SY, AExpV.ANum(1)),
)
assert smt.is_true(smt.simplify(imp_demo_if == _imp_if_expected))

_imp_while_expected = Com.CWhile(
    BExpV.BNeq(AExpV.AVar(SX), AExpV.ANum(0)),
    Com.CAss(SX, AExpV.AMinus(AExpV.AVar(SX), AExpV.ANum(1))),
)
assert smt.is_true(smt.simplify(imp_demo_while == _imp_while_expected))

_imp_ge_expected = Com.CIf(
    BExpV.BLe(AExpV.ANum(1), AExpV.AVar(SX)),
    Com.CSkip,
    Com.CSkip,
)
assert smt.is_true(smt.simplify(imp_demo_ge == _imp_ge_expected))


# --------------------------------------------------------------------
# More Imp programs (parsed).

plus2 = parse_imp("X := X + 2")
XtimesYinZ = parse_imp("Z := X * Y")
subtract_slowly_body = parse_imp("Z := Z - 1; X := X - 1")
subtract_slowly = parse_imp("while X <> 0 do Z := Z - 1; X := X - 1 end")
subtract_3_from_5_slowly = parse_imp(
    "X := 3; Z := 5; while X <> 0 do Z := Z - 1; X := X - 1 end"
)
loop = parse_imp("while true do skip end")


# --------------------------------------------------------------------
# Relational semantics matches functional evaluation.


@kd.Theorem(
    "ceval_wf "
    '(Ceval.CE_Seq (update empty_state "X" 2) '
    '(Ceval.CE_Ass "X" (AExpV.ANum 2) 2) '
    "(Ceval.CE_IfFalse "
    '(BExpV.BLe (AExpV.AVar "X") (AExpV.ANum 1)) '
    '(Com.CAss "Y" (AExpV.ANum 3)) '
    '(Com.CAss "Z" (AExpV.ANum 4)) '
    '(Ceval.CE_Ass "Z" (AExpV.ANum 4) 4))) '
    "c_example1 "
    'empty_state (update (update empty_state "X" 2) "Z" 4)'
)
def ceval_example1(pf):
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "ceval_wf "
    '(Ceval.CE_Seq (update empty_state "X" 0) '
    '(Ceval.CE_Ass "X" (AExpV.ANum 0) 0) '
    '(Ceval.CE_Seq (update (update empty_state "X" 0) "Y" 1) '
    '(Ceval.CE_Ass "Y" (AExpV.ANum 1) 1) '
    '(Ceval.CE_Ass "Z" (AExpV.ANum 2) 2))) '
    "c_example2 "
    'empty_state (update (update (update empty_state "X" 0) "Y" 1) "Z" 2)'
)
def ceval_example2(pf):
    pf.auto(by=BY_CEVAL)


# --------------------------------------------------------------------
# esimp experiments (existential synthesis for ceval_wf).

ev_ex2 = smt.Const("ev_ex2", Ceval)
st_ex2 = smt.Const("st_ex2", State)
esimp_ex2 = kdrw.esimp(
    [ev_ex2, st_ex2], ceval_wf(ev_ex2, c_example2, empty_state, st_ex2)
)
print(esimp_ex2)
"""
# Doesn't work too slow?
# Interesting, investigate later

ev_ex1 = smt.Const("ev_ex1", Ceval)
st_ex1 = smt.Const("st_ex1", State)
esimp_ex1 = kdrw.esimp(
    [ev_ex1],
    ceval_wf(
        ev_ex1,
        c_example1,
        empty_state,
        kd.lean('(update (update empty_state "X" 2) "Z" 4)'),
    ),
)
"""


# --------------------------------------------------------------------
# Reasoning About Imp Programs (attempts; keep for follow-up).

"""
@kd.Theorem(
    'forall (st st\' : State) (n : Int) (ev : Ceval), '
    'lookup st "X" = n -> '
    'ceval_wf ev plus2 st st\' -> '
    'lookup st\' "X" = n + 2'
)
def plus2_spec(pf):
    st, st1, n, ev = pf.fixes()
    pf.intros()
    pf.cases(ev)
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    'forall (st st\' : State) (x y : Int) (ev : Ceval), '
    'lookup st "X" = x -> '
    'lookup st "Y" = y -> '
    'ceval_wf ev XtimesYinZ st st\' -> '
    'lookup st\' "Z" = x * y'
)
def XtimesYinZ_spec(pf):
    st, st1, x, y, ev = pf.fixes()
    pf.intros()
    pf.cases(ev)
    pf.auto(by=BY_CEVAL)
"""


@kd.Theorem(
    "forall (st st' : State) (n : Int) (ev : Ceval), "
    'lookup st "X" = n -> '
    "ceval_wf ev plus2 st st' -> "
    'lookup st\' "X" = n + 2'
)
def plus2_spec(pf):
    pf.fixes()
    pf.auto(by=BY_CEVAL)


@kd.Theorem(
    "forall (st st' : State) (x y : Int) (ev : Ceval), "
    'lookup st "X" = x -> '
    'lookup st "Y" = y -> '
    "ceval_wf ev XtimesYinZ st st' -> "
    'lookup st\' "Z" = x * y'
)
def XtimesYinZ_spec(pf):
    pf.fixes()
    pf.auto(by=BY_CEVAL)
