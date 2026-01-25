# IndProp: Inductively Defined Propositions (partial translation from indprop.v)
# Goal: surface missing features / inconsistencies in knuckledragger as we go.

import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.nat as nat
from kdrag.theories.int import even

# --------------------------------------------------------------------
# Collatz conjecture (using Int for now; Nat would need more infrastructure).

# NOTE: This is a recursive definition encoded as axioms; there is no
# termination checker. Please inspect before we rely on it further.
div2 = kd.ldefine(
    "def div2 (n : Int) : Int := "
    "if n < 0 then 0 else "
    "if n = 0 then 0 else "
    "if n = 1 then 0 else div2 (n - 2) + 1"
)
print(div2.defn)

csf = kd.ldefine("def csf (n : Int) : Int := if even n then div2 n else (3 * n) + 1")

print(csf.defn)
# A deliberately failing attempt at a recursive definition (microlean has no fixpoint).
try:
    kd.ldefine(
        "def reaches1_in (n : Int) : Int := "
        "if n = 1 then 0 else 1 + reaches1_in (csf n)"
    )
except Exception as err:
    print("Expected failure (recursive definition):", err)


Collatz_holds_for = kd.inductive(
    "inductive Collatz_holds_for where "
    "| chf_one : Collatz_holds_for "
    "| chf_even : Collatz_holds_for -> Collatz_holds_for "
    "| chf_odd : Collatz_holds_for -> Collatz_holds_for"
)

collatz_holds_for_wf = kd.ldefine(
    "def collatz_holds_for_wf (ev : Collatz_holds_for) (n : Int) : Bool := "
    "match ev with "
    "| Collatz_holds_for.chf_one => n = 1 "
    "| Collatz_holds_for.chf_even sub => even n /\\ collatz_holds_for_wf sub (div2 n) "
    "| Collatz_holds_for.chf_odd sub => (even n = false) /\\ collatz_holds_for_wf sub ((3 * n) + 1)"
)

print(collatz_holds_for_wf.defn)


@kd.Theorem("exists (ev : Collatz_holds_for), collatz_holds_for_wf ev 1")
def collatz_1(pf):
    # Build the base-case evidence directly.
    pf.exists(Collatz_holds_for.chf_one)
    pf.auto(by=[collatz_holds_for_wf.defn])


try:
    # We cannot yet finish this without better evaluation of recursive defines.
    @kd.Theorem("exists (ev : Collatz_holds_for), collatz_holds_for_wf ev 12")
    def collatz_12(pf):
        pf.exists(
            Collatz_holds_for.chf_even(
                Collatz_holds_for.chf_even(Collatz_holds_for.chf_one)
            )
        )
        pf.auto(by=[collatz_holds_for_wf.defn, div2.defn])
except Exception as err:
    print("Expected failure (needs better Collatz evaluation):", err)


# --------------------------------------------------------------------
# A binary relation for <= on Nat.

Nat = nat.Nat
Z = Nat.Z
S = Nat.S

zero = Z
one = S(zero)
two = S(one)
three = S(two)
four = S(three)
five = S(four)

Le = kd.inductive("inductive Le where | le_n : Le | le_S : Le -> Le")

le_wf = kd.ldefine(
    "def le_wf (ev : Le) (n m : Nat) : Bool := "
    "match ev with "
    "| Le.le_n => n = m "
    "| Le.le_S sub => m.is_S /\\ le_wf sub n m.pred"
)


@kd.Theorem("exists (ev : Le), le_wf ev three five")
def le_3_5(pf):
    # Build evidence by peeling two successors off the RHS.
    pf.exists(Le.le_S(Le.le_S(Le.le_n)))
    pf.auto(by=[le_wf.defn])


# --------------------------------------------------------------------
# Transitive closure example (specialized to a concrete relation).

Person = kd.Enum("Person", "Sage Cleo Ridley Moss")

parent_of = kd.ldefine(
    "def parent_of (x y : Person) : Bool := "
    "if x = Person.Sage /\\ y = Person.Cleo then True else "
    "if x = Person.Sage /\\ y = Person.Ridley then True else "
    "if x = Person.Cleo /\\ y = Person.Moss then True else False"
)

ancestor_of = kd.inductive(
    "inductive ancestor_of where "
    "| t_step : ancestor_of "
    "| t_trans : Person -> ancestor_of -> ancestor_of -> ancestor_of"
)

ancestor_of_wf = kd.ldefine(
    "def ancestor_of_wf (ev : ancestor_of) (x y : Person) : Bool := "
    "match ev with "
    "| ancestor_of.t_step => parent_of x y "
    "| ancestor_of.t_trans mid ev1 ev2 => ancestor_of_wf ev1 x mid /\\ ancestor_of_wf ev2 mid y"
)


@kd.Theorem("exists (ev : ancestor_of), ancestor_of_wf ev Person.Sage Person.Moss")
def ancestor_of_ex(pf):
    # Build evidence by chaining the two parent_of steps.
    pf.exists(
        ancestor_of.t_trans(
            Person.Cleo,
            ancestor_of.t_step,
            ancestor_of.t_step,
        )
    )
    pf.auto(by=[ancestor_of_wf.defn, parent_of.defn])


# --------------------------------------------------------------------
# Evenness as an inductive proposition on Nat (explicit spine + wf).

Even = kd.inductive("inductive Even where | EvenZ : Even | EvenSS : Even -> Even")

EvenZ = Even.EvenZ
EvenSS = Even.EvenSS

even_wf = kd.ldefine(
    "def even_wf (ev : Even) (n : Nat) : Bool := "
    "match ev with "
    "| Even.EvenZ => n = Z "
    "| Even.EvenSS sub => n.is_S /\\ n.pred.is_S /\\ even_wf sub n.pred.pred"
)


@kd.Theorem("exists (e : Even), even_wf e four")
def ev_4(pf):
    # Build evidence with two applications of EvenSS.
    pf.exists(EvenSS(EvenSS(EvenZ)))
    pf.auto(by=[even_wf.defn])


@kd.Theorem(
    "forall (ev : Even) (n : Nat), even_wf ev (S (S n)) -> "
    "(exists (ev2 : Even), even_wf ev2 n)"
)
def evSS_ev(pf):
    ev, n = pf.fixes()
    pf.intros()
    pf.cases(ev)
    # EvenZ case: contradiction by unfolding even_wf.
    pf.auto(by=[even_wf.defn])
    # EvenSS case: choose the predecessor evidence.
    pf.exists(Even.EvenSS0(ev))
    pf.auto(by=[even_wf.defn])


@kd.Theorem("forall (ev : Even), even_wf ev (S Z) -> False")
def one_not_even(pf):
    ev = pf.fix()
    pf.intros()
    pf.cases(ev)
    pf.auto(by=[even_wf.defn])
    pf.auto(by=[even_wf.defn])


@kd.Theorem(
    "forall (ev : Even) (n : Nat), even_wf ev n -> even_wf (Even.EvenSS ev) (S (S n))"
)
def even_SS(pf):
    ev, n = pf.fixes()
    pf.intros()
    # Unfold even_wf and let Z3 discharge the constructor case.
    pf.auto(by=[even_wf.defn])


@kd.Theorem(
    "forall (ev : Even) (n : Nat), even_wf ev n -> "
    "even_wf (Even.EvenSS (Even.EvenSS ev)) (S (S (S (S n))))"
)
def even_plus4(pf):
    ev, n = pf.fixes()
    pf.intros()
    # Two applications of the EvenSS constructor.
    pf.auto(by=[even_wf.defn])


# --------------------------------------------------------------------
# More le_wf examples.


@kd.Theorem("forall (n : Nat), exists (ev : Le), le_wf ev n n")
def le_refl(pf):
    _n = pf.fix()
    pf.exists(Le.le_n)
    pf.auto(by=[le_wf.defn])


@kd.Theorem("forall (ev : Le) (n m : Nat), le_wf ev n m -> le_wf (Le.le_S ev) n (S m)")
def le_step(pf):
    ev, n, m = pf.fixes()
    pf.intros()
    pf.auto(by=[le_wf.defn])


# --------------------------------------------------------------------
# Inversion-style lemmas.


@kd.Theorem(
    "forall (ev : Even) (n : Nat), even_wf ev n -> "
    "(n = Z \\/ (exists (n2 : Nat), n = S (S n2)))"
)
def ev_inversion(pf):
    ev, n = pf.fixes()
    pf.intros()
    pf.cases(ev)
    # EvenZ: left branch.
    pf.left()
    pf.auto(by=[even_wf.defn])
    # EvenSS: right branch with n2 = n.pred.pred.
    pf.right()
    pf.exists(n.pred.pred)
    pf.auto(by=[even_wf.defn])


@kd.Theorem(
    "forall (ev : Le) (n m : Nat), le_wf ev n m -> "
    "(n = m \\/ (exists (m2 : Nat), m = S m2))"
)
def le_inversion(pf):
    ev, n, m = pf.fixes()
    pf.intros()
    pf.cases(ev)
    # le_n case.
    pf.left()
    pf.auto(by=[le_wf.defn])
    # le_S case.
    pf.right()
    pf.exists(m.pred)
    pf.auto(by=[le_wf.defn])


# --------------------------------------------------------------------
# Permutations of triples (Perm3 on Int sequences).

IntSeq = smt.SeqSort(smt.IntSort())

Perm3 = kd.inductive(
    "inductive Perm3 where "
    "| perm3_swap12 : Perm3 "
    "| perm3_swap23 : Perm3 "
    "| perm3_trans : IntSeq -> Perm3 -> Perm3 -> Perm3"
)

triple = kd.ldefine("def triple (a b c : Int) : IntSeq := [a, b, c]")

perm3_wf = kd.ldefine(
    "def perm3_wf (ev : Perm3) (l1 l2 : IntSeq) : Bool := "
    "match ev with "
    "| Perm3.perm3_swap12 => "
    "    exists (a b c : Int), l1 = triple a b c /\\ l2 = triple b a c "
    "| Perm3.perm3_swap23 => "
    "    exists (a b c : Int), l1 = triple a b c /\\ l2 = triple a c b "
    "| Perm3.perm3_trans mid ev12 ev23 => "
    "    perm3_wf ev12 l1 mid /\\ perm3_wf ev23 mid l2"
)

t123 = triple(1, 2, 3)
t213 = triple(2, 1, 3)
t231 = triple(2, 3, 1)
t132 = triple(1, 3, 2)
t321 = triple(3, 2, 1)


@kd.Theorem("perm3_wf Perm3.perm3_swap12 t123 t213")
def perm3_swap12_ex(pf):
    pf.auto(by=[perm3_wf.defn, triple.defn])


@kd.Theorem("perm3_wf Perm3.perm3_swap23 t123 t132")
def perm3_swap23_ex(pf):
    pf.auto(by=[perm3_wf.defn, triple.defn])


@kd.Theorem("exists (ev : Perm3), perm3_wf ev t123 t231")
def perm3_ex1(pf):
    pf.exists(Perm3.perm3_trans(t213, Perm3.perm3_swap12, Perm3.perm3_swap23))
    pf.auto(by=[perm3_wf.defn, triple.defn])


@kd.Theorem("exists (ev : Perm3), perm3_wf ev t123 t123")
def perm3_refl(pf):
    # Two swaps on adjacent positions return to the original list.
    pf.exists(Perm3.perm3_trans(t213, Perm3.perm3_swap12, Perm3.perm3_swap12))
    pf.auto(by=[perm3_wf.defn, triple.defn])


@kd.Theorem("exists (ev : Perm3), perm3_wf ev t123 t321")
def perm3_rev(pf):
    pf.exists(
        Perm3.perm3_trans(
            t231,
            Perm3.perm3_trans(t213, Perm3.perm3_swap12, Perm3.perm3_swap23),
            Perm3.perm3_swap12,
        )
    )
    pf.auto(by=[perm3_wf.defn, triple.defn])


# --------------------------------------------------------------------
# Regular expressions (inductive evidence + wf predicate).

RegExp = kd.inductive(
    "inductive RegExp where "
    "| EmptySet : RegExp "
    "| EmptyStr : RegExp "
    "| Char : Int -> RegExp "
    "| App : RegExp -> RegExp -> RegExp "
    "| Union : RegExp -> RegExp -> RegExp "
    "| Star : RegExp -> RegExp"
)

ExpMatch = kd.inductive(
    "inductive ExpMatch where "
    "| MEmpty : ExpMatch "
    "| MChar : Int -> ExpMatch "
    "| MApp : IntSeq -> IntSeq -> RegExp -> RegExp -> ExpMatch -> ExpMatch -> ExpMatch "
    "| MUnionL : RegExp -> RegExp -> ExpMatch -> ExpMatch "
    "| MUnionR : RegExp -> RegExp -> ExpMatch -> ExpMatch "
    "| MStar0 : RegExp -> ExpMatch "
    "| MStarApp : IntSeq -> IntSeq -> RegExp -> ExpMatch -> ExpMatch -> ExpMatch"
)

empty_intseq = smt.Empty(IntSeq)

exp_match_wf = kd.ldefine(
    "def exp_match_wf (ev : ExpMatch) (s : IntSeq) (re : RegExp) : Bool := "
    "match ev with "
    "| ExpMatch.MEmpty => s = empty_intseq /\\ re = RegExp.EmptyStr "
    "| ExpMatch.MChar c => s = [c] /\\ re = RegExp.Char c "
    "| ExpMatch.MApp s1 s2 re1 re2 ev1 ev2 => "
    "    s = s1 + s2 /\\ re = RegExp.App re1 re2 /\\ "
    "    exp_match_wf ev1 s1 re1 /\\ exp_match_wf ev2 s2 re2 "
    "| ExpMatch.MUnionL re1 re2 ev1 => "
    "    re = RegExp.Union re1 re2 /\\ exp_match_wf ev1 s re1 "
    "| ExpMatch.MUnionR re1 re2 ev2 => "
    "    re = RegExp.Union re1 re2 /\\ exp_match_wf ev2 s re2 "
    "| ExpMatch.MStar0 re1 => s = empty_intseq /\\ re = RegExp.Star re1 "
    "| ExpMatch.MStarApp s1 s2 re1 ev1 ev2 => "
    "    s = s1 + s2 /\\ re = RegExp.Star re1 /\\ "
    "    exp_match_wf ev1 s1 re1 /\\ exp_match_wf ev2 s2 (RegExp.Star re1)"
)


@kd.Theorem("exp_match_wf ExpMatch.MEmpty empty_intseq RegExp.EmptyStr")
def exp_match_empty(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem("exp_match_wf (ExpMatch.MChar 1) [1] (RegExp.Char 1)")
def exp_match_char(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf "
    "(ExpMatch.MApp [1] [2] (RegExp.Char 1) (RegExp.Char 2) "
    "(ExpMatch.MChar 1) (ExpMatch.MChar 2)) "
    "[1, 2] (RegExp.App (RegExp.Char 1) (RegExp.Char 2))"
)
def exp_match_app(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf (ExpMatch.MStar0 (RegExp.Char 1)) "
    "empty_intseq (RegExp.Star (RegExp.Char 1))"
)
def exp_match_star0(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf "
    "(ExpMatch.MUnionL (RegExp.Char 1) (RegExp.Char 2) (ExpMatch.MChar 1)) "
    "[1] (RegExp.Union (RegExp.Char 1) (RegExp.Char 2))"
)
def exp_match_union_l(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf "
    "(ExpMatch.MUnionR (RegExp.Char 1) (RegExp.Char 2) (ExpMatch.MChar 2)) "
    "[2] (RegExp.Union (RegExp.Char 1) (RegExp.Char 2))"
)
def exp_match_union_r(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf "
    "(ExpMatch.MStarApp [1] empty_intseq (RegExp.Char 1) "
    "(ExpMatch.MChar 1) (ExpMatch.MStar0 (RegExp.Char 1))) "
    "[1] (RegExp.Star (RegExp.Char 1))"
)
def exp_match_star1(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf "
    "(ExpMatch.MStarApp [1] [1] (RegExp.Char 1) "
    "(ExpMatch.MChar 1) "
    "(ExpMatch.MStarApp [1] empty_intseq (RegExp.Char 1) "
    "(ExpMatch.MChar 1) (ExpMatch.MStar0 (RegExp.Char 1)))) "
    "[1, 1] (RegExp.Star (RegExp.Char 1))"
)
def exp_match_star2(pf):
    pf.auto(by=[exp_match_wf.defn])


@kd.Theorem(
    "exp_match_wf "
    "(ExpMatch.MApp [1, 2] [3] "
    "(RegExp.App (RegExp.Char 1) (RegExp.Char 2)) (RegExp.Char 3) "
    "(ExpMatch.MApp [1] [2] (RegExp.Char 1) (RegExp.Char 2) "
    "(ExpMatch.MChar 1) (ExpMatch.MChar 2)) "
    "(ExpMatch.MChar 3)) "
    "[1, 2, 3] "
    "(RegExp.App (RegExp.App (RegExp.Char 1) (RegExp.Char 2)) (RegExp.Char 3))"
)
def exp_match_app3(pf):
    pf.auto(by=[exp_match_wf.defn])
