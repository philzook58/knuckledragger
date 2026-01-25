import kdrag.parsers as parsers
import kdrag.solvers.prolog as prolog
import kdrag.parsers.tptp as tptp
import kdrag.parsers.smtlib as smtlib
import kdrag.parsers.microlean as microlean
import kdrag.theories.real.seq as seq
import kdrag.theories.nat as nat
import lark
import kdrag.smt as smt
import kdrag as kd

def test_prolog():
    ex1 = """add(z,Y,Y).
    add(s(X),Y,s(Z)) :- add(X,Y,Z).
    ?- add(s(s(z)),s(z),X)."""
    t = prolog.parser.parse(ex1)
    Term = prolog.Term
    add = smt.Function("add", Term, Term, Term, smt.BoolSort())
    s = smt.Function("s", Term, Term)
    z, X, Y, Z = smt.Consts("z X Y Z", Term)
    assert prolog.interp(t)[0][0].eq(smt.ForAll([Y], add(z, Y, Y)))
    print(prolog.interp(t)[0][1])
    # ordering of [X,Y,Z] is not stable in quantifier.
    #assert prolog.interp(t)[0][1].eq(smt.ForAll([X,Y,Z],
    #    smt.Implies( smt.And(add(X, Y, Z)), add(s(X), Y, s(Z)))))





def test_smtlib():
    ex1 = """
    (assert (= 1 1))
    (check-sat)
    (get-model)
    """
    t = smtlib.parser.parse(ex1)


def test_microlean_did_you_mean():
    ex1 = "has_lim (fun (n : Int) => n) 0"
    try:
        microlean.parse(ex1, {}, {"seq": seq})
    except NameError as exc:
        assert "seq.has_lim" in str(exc)
    else:
        raise AssertionError("Expected NameError with suggestion")


def test_microlean_decimal_is_real():
    t = microlean.parse("1.0", {})
    assert t.eq(smt.RealVal("1.0"))

def test_microlean_match_datatype():
    n = smt.Const("n", nat.Nat)
    m = smt.Const("m", nat.Nat)
    parsed = microlean.lean(
        "match n with | nat.Nat.S m => m | nat.Nat.Z => nat.Nat.Z"
    )
    default = parsed
    while smt.is_if(default):
        default = default.arg(2)
    expected = kd.datatype.datatype_match_(
        n, (nat.Nat.S(m), m), (nat.Nat.Z, nat.Nat.Z), default=default
    )
    assert parsed.eq(expected)

def test_ldefine():
    kd.ldefine("def foo192 (x : Int) : Int := x + 1")
    y = smt.Bool("y")
    assert microlean.define("def bar192 (x : Int) : Int := if y then x else -x") == smt.Function(
        "bar192", smt.IntSort(), smt.IntSort())
    assert kd.ldefine("def bar192 (x : Int) : Int := if y then x else -x") == smt.Function(
        "bar192", smt.IntSort(), smt.IntSort())

# https://tptp.org/UserDocs/TPTPWorldTutorial/LogicFOF.html
fof_example = """
fof(different_people,axiom,
    ( iokaste != oedipus & iokaste != polyneikes & iokaste != thersandros
    & oedipus != polyneikes & oedipus != thersandros
    & polyneikes != thersandros ) ).
fof(iokaste_oedipus,axiom,
    ( parent_of(iokaste,oedipus) & parent_of(iokaste,polyneikes) ) ).
fof(oedipus_polyneikes,axiom,
    parent_of(oedipus,polyneikes) ).
fof(polyneikes_thersandros,axiom,
    parent_of(polyneikes,thersandros) ).
fof(no_self_parent,axiom,
    ! [X] : ~ parent_of(X,X) ).
fof(oedipus_patricidal,axiom,
    patricide(oedipus) ).
fof(thersandros_not_patricidal,axiom,
    ~ patricide(thersandros) ).
fof(iokaste_parent_particide_parent_not_patricide,conjecture,
    ? [P,NP] :
      ( parent_of(iokaste,P) & patricide(P) & parent_of(P,NP)
      & ~ patricide(NP) ) ).  
"""

fof_example1 = """
fof(usa,axiom, country(usa) ).
fof(country_big_city,axiom,
    ! [C] : ( country(C) => ( big_city(capital_of(C)) & beautiful(capital_of(C)) ) ) ).
fof(usa_capital_axiom,axiom, 
    ? [C] : ( city(C) & C = capital_of(usa) ) ).
fof(crime_axiom,axiom,
    ! [C] : ( big_city(C) => has_crime(C) ) ).
fof(big_city_city,axiom,
    ! [C] : ( big_city(C) => city(C) ) ).

fof(some_beautiful_crime,conjecture,
    ? [C] : ( city(C) & beautiful(C) & has_crime(C) ) ).
"""

def test_tptp():
    tree = tptp.fof_parser.parse(fof_example)
    z3_terms = tptp.to_z3(tree)
    parsed = z3_terms

    iokaste, oedipus, polyneikes, thersandros = smt.Consts(
        "iokaste oedipus polyneikes thersandros", tptp.T
    )
    X, P, NP = smt.Consts("X P NP", tptp.T)
    parent_of = smt.Function("parent_of", tptp.T, tptp.T, smt.BoolSort())
    patricide = smt.Function("patricide", tptp.T, smt.BoolSort())

    expected = [
        (
            "different_people",
            tptp.FormulaRole.AXIOM,
            smt.And(
                iokaste != oedipus,
                iokaste != polyneikes,
                iokaste != thersandros,
                oedipus != polyneikes,
                oedipus != thersandros,
                polyneikes != thersandros,
            ),
        ),
        (
            "iokaste_oedipus",
            tptp.FormulaRole.AXIOM,
            smt.And(
                parent_of(iokaste, oedipus),
                parent_of(iokaste, polyneikes),
            ),
        ),
        ("oedipus_polyneikes", tptp.FormulaRole.AXIOM, parent_of(oedipus, polyneikes)),
        ("polyneikes_thersandros", tptp.FormulaRole.AXIOM, parent_of(polyneikes, thersandros)),
        ("no_self_parent", tptp.FormulaRole.AXIOM, smt.ForAll([X], smt.Not(parent_of(X, X)))),
        ("oedipus_patricidal", tptp.FormulaRole.AXIOM, patricide(oedipus)),
        ("thersandros_not_patricidal", tptp.FormulaRole.AXIOM, smt.Not(patricide(thersandros))),
        (
            "iokaste_parent_particide_parent_not_patricide",
            tptp.FormulaRole.CONJECTURE,
            smt.Exists(
                [P, NP],
                smt.And(
                    parent_of(iokaste, P),
                    patricide(P),
                    parent_of(P, NP),
                    smt.Not(patricide(NP)),
                ),
            ),
        ),
    ]

    assert len(parsed) == len(expected)
    for entry, (e_name, e_role, e_formula) in zip(parsed, expected, strict=True):
        assert entry.name == e_name
        assert entry.role == e_role
        assert entry.formula.eq(e_formula)

tff_example1 = """
tff(human_type,type,human: $tType).
tff(grade_type,type,grade: $tType).
tff(john_decl,type,john: human).
tff(a_decl,type,a: grade).
tff(f_decl,type,f: grade).
tff(grade_of_decl,type,grade_of: human > grade).
tff(created_equal_decl,type,created_equal: (human * human) > $o).

tff(all_created_equal,axiom,
    ! [H1:human,H2:human] : created_equal(H1,H2) ).
tff(john_got_an_f,axiom,
    grade_of(john) = f ).
tff(someone_got_an_a,axiom,
    ? [H:human] : grade_of(H) = a ).
tff(a_is_not_f,axiom,
    a != f ).

tff(there_is_someone_else,conjecture,
    ? [H:human] :
      ( H != john
      & created_equal(H,john) ) ).
"""

# https://tptp.org/UserDocs/TPTPWorldTutorial/LogicTFF.html
tff_example = """
tff(human_type,type,      human: $tType ).
tff(cat_type,type,        cat: $tType ).
tff(jon_decl,type,        jon: human ).
tff(garfield_decl,type,   garfield: cat ).
tff(arlene_decl,type,     arlene: cat ).
tff(nermal_decl,type,     nermal: cat ).
tff(loves_decl,type,      loves: cat > cat ).
tff(owns_decl,type,       owns: ( human * cat ) > $o ).

tff(only_jon,axiom, ! [H: human] : H = jon ).

tff(only_garfield_and_arlene_and_nermal,axiom,
    ! [C: cat] :
      ( C = garfield | C = arlene | C = nermal ) ).

tff(distinct_cats,axiom,
    ( garfield != arlene & arlene != nermal
    & nermal != garfield ) ).

tff(jon_owns_garfield_not_arlene,axiom,
    ( owns(jon,garfield) & ~ owns(jon,arlene) ) ).

tff(all_cats_love_garfield,axiom,
    ! [C: cat] : ( loves(C) = garfield ) ).

tff(jon_owns_garfields_lovers,conjecture,
    ! [C: cat] :
      ( ( loves(C) = garfield & C != arlene )
     => owns(jon,C) ) ).
"""

def test_tptp_tff():
    tree = tptp.fof_parser.parse(tff_example)
    z3_terms = tptp.to_z3(tree)
    parsed = z3_terms

    human = smt.DeclareSort("human")
    cat = smt.DeclareSort("cat")
    jon, = smt.Consts("jon", human)
    garfield, arlene, nermal = smt.Consts("garfield arlene nermal", cat)
    H = smt.Const("H", human)
    C = smt.Const("C", cat)
    loves = smt.Function("loves", cat, cat)
    owns = smt.Function("owns", human, cat, smt.BoolSort())

    expected = [
        ("only_jon", tptp.FormulaRole.AXIOM, smt.ForAll([H], H == jon)),
        (
            "only_garfield_and_arlene_and_nermal",
            tptp.FormulaRole.AXIOM,
            smt.ForAll([C], smt.Or(C == garfield, C == arlene, C == nermal)),
        ),
        (
            "distinct_cats",
            tptp.FormulaRole.AXIOM,
            smt.And(garfield != arlene, arlene != nermal, nermal != garfield),
        ),
        (
            "jon_owns_garfield_not_arlene",
            tptp.FormulaRole.AXIOM,
            smt.And(owns(jon, garfield), smt.Not(owns(jon, arlene))),
        ),
        ("all_cats_love_garfield", tptp.FormulaRole.AXIOM, smt.ForAll([C], loves(C) == garfield)),
        (
            "jon_owns_garfields_lovers",
            tptp.FormulaRole.CONJECTURE,
            smt.ForAll(
                [C],
                smt.Implies(
                    smt.And(loves(C) == garfield, C != arlene),
                    owns(jon, C),
                ),
            ),
        ),
    ]

    assert len(parsed) == len(expected)
    for entry, (e_name, e_role, e_formula) in zip(parsed, expected, strict=True):
        assert entry.name == e_name
        assert entry.role == e_role
        assert entry.formula.eq(e_formula)


group_cnf = r"""
%--------------------------------------------------------------------------
% File     : GRP001-0 : TPTP v8.2.0. Released v1.0.0.
% Domain   : Group theory (Monoids)
% Axioms   : Monoid axioms
% Version  : [MOW76] axioms.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [Ver93] Veroff (1993), Email to G. Sutcliffe
% Source   : [MOW76]
% Names    :

% Status   : Satisfiable
% Syntax   : Number of clauses     :    6 (   3 unt;   0 nHn;   3 RR)
%            Number of literals    :   14 (   1 equ;   8 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-3 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-2 aty)
%            Number of variables   :   20 (   0 sgn)
% SPC      : 

% Comments : [Ver93] pointed out that the traditional labelling of the
%            closure and well_definedness axioms was wrong. The correct
%            labelling indicates that product is a total function.
%          : I cut down the [MOW76] group axioms for this.
%--------------------------------------------------------------------------
cnf(left_identity,axiom,
    product(identity,X,X) ).

cnf(right_identity,axiom,
    product(X,identity,X) ).

%----This axiom is called closure or totality in some axiomatisations
cnf(total_function1,axiom,
    product(X,Y,multiply(X,Y)) ).

%----This axiom is called well_definedness in some axiomatisations
cnf(total_function2,axiom,
    ( ~ product(X,Y,Z)
    | ~ product(X,Y,W)
    | Z = W ) ).

cnf(associativity1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

%--------------------------------------------------------------------------

"""


def test_tptp_group_cnf():
    tree = tptp.fof_parser.parse(group_cnf)
    z3_terms = tptp.to_z3(tree)
    parsed = z3_terms

    T = tptp.T
    identity = smt.Const("identity", T)
    X, Y, Z, W, U, V = smt.Consts("X Y Z W U V", T)
    multiply = smt.Function("multiply", T, T, T)
    product = smt.Function("product", T, T, T, smt.BoolSort())

    expected = [
        ("left_identity", tptp.FormulaRole.AXIOM, product(identity, X, X)),
        ("right_identity", tptp.FormulaRole.AXIOM, product(X, identity, X)),
        ("total_function1", tptp.FormulaRole.AXIOM, product(X, Y, multiply(X, Y))),
        (
            "total_function2",
            tptp.FormulaRole.AXIOM,
            smt.Or(
                smt.Not(product(X, Y, Z)),
                smt.Not(product(X, Y, W)),
                Z == W,
            ),
        ),
        (
            "associativity1",
            tptp.FormulaRole.AXIOM,
            smt.Or(
                smt.Not(product(X, Y, U)),
                smt.Not(product(Y, Z, V)),
                smt.Not(product(U, Z, W)),
                product(X, V, W),
            ),
        ),
        (
            "associativity2",
            tptp.FormulaRole.AXIOM,
            smt.Or(
                smt.Not(product(X, Y, U)),
                smt.Not(product(Y, Z, V)),
                smt.Not(product(X, V, W)),
                product(U, Z, W),
            ),
        ),
    ]

    assert len(parsed) == len(expected)
    for entry, (e_name, e_role, e_formula) in zip(parsed, expected, strict=True):
        assert entry.name == e_name
        assert entry.role == e_role
        assert entry.formula.eq(e_formula)


example_thf = """
%------------------------------------------------------------------------------
thf(beverage_type,type,beverage: $tType).
thf(syrup_type,type,syrup: $tType).
thf(coffee_decl,type,coffee: beverage).
thf(mix_decl,type,mix: beverage > syrup > beverage).
thf(heat_decl,type,heat: beverage > beverage ).
thf(heated_mix_decl,type,heated_mix: beverage > syrup > beverage).
thf(hot_decl,type,hot: beverage > $o).

thf(heated_mix,axiom,
    heated_mix = ( ^ [B: beverage,S :syrup] : ( heat @ ( mix @ B @ S ))) ).

thf(hot_mixture,axiom,
    ! [B: beverage,S: syrup] : ( hot @ ( heated_mix @ B @ S ) ) ).

thf(heated_coffee_mix,axiom,
    ! [S: syrup] : ( ( heated_mix @ coffee @ S ) = coffee ) ).

thf(hot_coffee,conjecture,
    ? [Mixture: syrup > beverage] :
    ! [S: syrup] :
        ( ( ( Mixture @ S ) = coffee )
        & ( hot @ ( Mixture @ S ) ) ) ).
%------------------------------------------------------------------------------
"""


def test_tptp_thf():
    tree = tptp.fof_parser.parse(example_thf)
    z3_terms = tptp.to_z3(tree)
    parsed = z3_terms

    beverage = smt.DeclareSort("beverage")
    syrup = smt.DeclareSort("syrup")
    coffee = smt.Const("coffee", beverage)
    B = smt.Const("B", beverage)
    S = smt.Const("S", syrup)
    mix = smt.Const("mix", smt.ArraySort(beverage, smt.ArraySort(syrup, beverage)))
    heat = smt.Const("heat", smt.ArraySort(beverage, beverage))
    heated_mix = smt.Const(
        "heated_mix", smt.ArraySort(beverage, smt.ArraySort(syrup, beverage))
    )
    hot = smt.Const("hot", smt.ArraySort(beverage, smt.BoolSort()))
    Mixture = smt.Const("Mixture", smt.ArraySort(syrup, beverage))

    mix_b = smt.Select(mix, B)
    mix_b_s = smt.Select(mix_b, S)
    heat_mix = smt.Select(heat, mix_b_s)
    heated_mix_def = smt.Lambda([B], smt.Lambda([S], heat_mix))

    heated_mix_b = smt.Select(heated_mix, B)
    heated_mix_b_s = smt.Select(heated_mix_b, S)
    hot_heated_mix = smt.Select(hot, heated_mix_b_s)

    heated_mix_coffee = smt.Select(heated_mix, coffee)
    heated_mix_coffee_s = smt.Select(heated_mix_coffee, S)

    mixture_s = smt.Select(Mixture, S)
    hot_mixture_s = smt.Select(hot, mixture_s)

    expected = [
        ("heated_mix", tptp.FormulaRole.AXIOM, smt.Eq(heated_mix, heated_mix_def)),
        ("hot_mixture", tptp.FormulaRole.AXIOM, smt.ForAll([B, S], hot_heated_mix)),
        (
            "heated_coffee_mix",
            tptp.FormulaRole.AXIOM,
            smt.ForAll([S], smt.Eq(heated_mix_coffee_s, coffee)),
        ),
        (
            "hot_coffee",
            tptp.FormulaRole.CONJECTURE,
            smt.Exists(
                [Mixture],
                smt.ForAll(
                    [S],
                    smt.And(mixture_s == coffee, hot_mixture_s),
                ),
            ),
        ),
    ]

    assert len(parsed) == len(expected)
    for entry, (e_name, e_role, e_formula) in zip(parsed, expected, strict=True):
        assert entry.name == e_name
        assert entry.role == e_role
        assert entry.formula.eq(e_formula)
