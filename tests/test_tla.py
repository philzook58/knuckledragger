import kdrag.solvers.tla as tla
import kdrag.smt as smt
import kdrag as kd
hour_clock = r"""
---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
          (* Alternately expressed as: hr' = (hr % 12) + 1 *)

HC == HCini /\ [][HCnxt]_hr

------------------------------

THEOREM  HC => []HCini

==========================
"""

hour_cfg = r"""
SPECIFICATION HC
   \* This statement tells TLC that HC is the specification that it
   \* should check.

INVARIANT HCini
"""

def test_tla_to_xml():
    with open("/tmp/HourClock.tla", "w") as f:
        f.write(hour_clock)
    xml = tla.tla_to_xml("/tmp/HourClock.tla")
    mod = tla.Module.of_file("/tmp/HourClock.tla")
    assert mod.name == "HourClock"
    assert mod.variables == ["hr"]
    assert list(mod.definitions.keys()) == ["HCini", "HCnxt", "HC"]
    assert mod.theorems == [tla.App("=>", [tla.App("HC", []), tla.App("[]", [tla.App("HCini", [])])])]
    hr, hr1 = smt.Ints("hr hr'")
    decls = {"hr": hr}
    assert mod.action("HCini", decls).sort() == smt.BoolSort()
    assert mod.action("HCnxt", decls).eq(hr1 == smt.If(hr == 12, 1, hr + 1))
    #assert mod.infer_sorts(typeok="HCini") == decls

    mod.infer_sorts()
    assert mod.decls == {"HCini": smt.Function("HCini", smt.BoolSort()), "HCnxt": smt.Function("HCnxt", smt.BoolSort()), 
                         "HC": smt.Function("HC", smt.BoolSort()), "hr": smt.Function("hr", smt.IntSort())}


    #with open("/tmp/HourClock.cfg", "w") as f:
    #    f.write(hour_cfg)
    #tla.check("/tmp/HourClock.tla")


# https://learntla.com/core/operators.html
mytest = r"""
---- MODULE MyTest ----
EXTENDS Integers, Sequences
VARIABLES is_unique
VARIABLES biz, S

VARIABLES flag
TypeOKFlag == /\ flag \in [{0, 1} -> BOOLEAN]

TypeInvariant == /\ is_unique \in BOOLEAN
                 /\ biz \in 1..10

MinutesToSeconds(m) == m * 60

Abs(x) == IF x < 0 THEN -x ELSE x
Xor(A, B) == A = ~B



ToSeconds(time) == time[1]*3600 + time[2]*60 + time[3]
Earlier(t1, t2) == ToSeconds(t1) < ToSeconds(t2)

E1 == {1, 3} \union {1, 5}
E2 == {1, 3} \intersect {1, 5}
E3 == {1, 3} \ {1, 5}


E5 == S \o <<"b", "c">>
E6 == Head(S)
E7 == Tail(<<1, 2, 3>>)
E8 == Len(S)
(* E9 == SubSeq(<<1, 3, 5>>, 1, 2) TODO. *)
E10 == Append(S, "b")

ClockType == (0..23) \X (0..59) \X (0..59)

\* TODO

\* Map
Squares == {x*x: x \in 1..4}

\* Filter
Evens == {x \in 1..4: x % 2 = 0 }

ToClock(seconds) ==
  LET seconds_per_day == 86400
  IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day

struct == [a |-> 1, b |-> {}]
Accounts == {"checking", "savings"}
BankTransactionType == [acct: Accounts, amnt: 1..10, type: {"deposit", "withdraw"}]

myrange == 1..3
TestQuant == \A x \in myrange, y \in myrange: x + y > 0
\* TestQuant == \A x \in myrange, y \in 1..x: x + y > 0  fails, so i think no telescoping allowed


FunCon == [self \in 1..2 |-> "alice"][1] = "alice"

\* Exception Syntax
TestExcept == [[p \in 1..2 |-> "Foo"] EXCEPT ![1] = "Done"]


SetOfFunc == [p \in {0,1} |-> TRUE] \in [{0, 1} -> BOOLEAN]
Equiv == TRUE <=> FALSE
Implies == TRUE => FALSE


==========================
"""

def test_tla_mytest():
    with open("/tmp/MyTest.tla", "w") as f:
        f.write(mytest)
    mod = tla.Module.of_file("/tmp/MyTest.tla")
    mod.declare_vars([smt.Const("S", smt.SeqSort(smt.StringSort()))])
    mod.infer_sorts()
    assert mod.decls["is_unique"].range() == smt.BoolSort() and mod.decls["biz"].range() == smt.IntSort()
    assert mod.name == "MyTest"
    assert set(mod.variables) == {"biz", "is_unique", "S", "flag"}
    #assert list(mod.definitions.keys()) == ["TypeInvariant", "MinutesToSeconds"]
    assert mod.theorems == []
    #decls = mod.infer_sorts(typeok="TypeInvariant")
    decls = mod.decls #{ k : smt.Const(k, sort) for k,sort in mod.sorts.items()}
    #assert decls == {"is_unique": smt.Const("is_unique", smt.BoolSort())}
    assert mod.action("TypeInvariant", decls).sort() == smt.BoolSort()
    assert mod.def_params["MinutesToSeconds"] == ["m"]

    assert mod.operator("Abs", {"x": smt.Int("x")}).eq(smt.If(smt.Int("x") < smt.IntVal(0), -smt.Int("x"), smt.Int("x")))
    assert mod.operator("Xor", {"A": smt.Bool("A"), "B": smt.Bool("B")}).eq(smt.Bool("A") == ~smt.Bool("B"))

    time = smt.Const("time", smt.SeqSort(smt.IntSort()))
    assert mod.operator("ToSeconds", {"time": time.decl()}).eq(
        (time[smt.IntVal(1) - smt.IntVal(1)] * smt.IntVal(3600) + time[smt.IntVal(2) - smt.IntVal(1)] * smt.IntVal(60)) + time[smt.IntVal(3) - smt.IntVal(1)]
    )

    s13 = smt.SetAdd(smt.SetAdd(smt.EmptySet(smt.IntSort()), smt.IntVal(1)), smt.IntVal(3))
    s15 = smt.SetAdd(smt.SetAdd(smt.EmptySet(smt.IntSort()), smt.IntVal(1)), smt.IntVal(5))
    assert mod.operator("E1", {}).eq(smt.SetUnion(s13, s15))
    assert mod.operator("E2", {}).eq(smt.SetIntersect(s13, s15))
    assert mod.operator("E3", {}).eq(smt.SetDifference(s13, s15))
    S = smt.Const("S", smt.SeqSort(smt.StringSort()))
    assert mod.operator("E5", {"S": S}).eq(smt.Concat(S, kd.seq("b", "c")))
    assert mod.operator("E6", {"S": S}).eq(S[0])
    assert mod.operator("E7", {}).eq(kd.Tail(kd.seq(1, 2, 3)))
    assert mod.operator("E8", {"S": S}).eq(smt.Length(S))

    assert mod.operator("E10", {"S": S}).eq(smt.Concat(S, kd.seq("b")))

    # TODO
    #assert mod.operator("ClockType", {}).sort() == smt.TupleSort([smt.IntSort(), smt.IntSort(), smt.IntSort()])

    #assert mod.operator("Squares", {}).eq(smt.EmptySet(smt.IntSort()))

    assert mod.operator("struct", {}, sort=kd.AStruct(a=smt.IntSort(), b=smt.SetSort(smt.IntSort()))).eq(kd.astruct(a=smt.IntVal(1), b=smt.EmptySet(smt.IntSort())))
    assert isinstance(mod.operator("BankTransactionType", {"Accounts" : smt.EmptySet(smt.StringSort())}).sort(), smt.ArraySortRef)

    x,y = smt.Ints("x y")
    myrange = smt.Const("myrange", smt.SetSort(smt.IntSort()))

    #print("TestQuant", mod.operator("TestQuant", {}))
    assert mod.operator("TestQuant", {"myrange" : myrange}).is_forall()


    self = smt.Int("self")
    mod.operator("FunCon", {}).eq(smt.Eq(smt.Select(smt.Lambda(self, smt.StringVal("alice")), smt.IntVal(1)), smt.StringVal("alice")))
    p = smt.Int("p")
    assert mod.operator("TestExcept", {}).eq(smt.Store(smt.Lambda([p], smt.StringVal("Foo")), 1, smt.StringVal("Done")))

    assert mod.action("SetOfFunc", {}).arg(1).is_lambda()
    kd.prove(mod.action("SetOfFunc"))

    assert mod.action("Equiv", {}).eq(smt.Eq(smt.BoolVal(True), smt.BoolVal(False)))
    assert mod.action("Implies", {}).eq(smt.Implies(smt.BoolVal(True), smt.BoolVal(False)))


pluscal1 = r"""
---- MODULE pluscal ----
EXTENDS Integers, TLC

(* --algorithm pluscal
variables
 x = 2;
 y = TRUE;

begin
  A:
    x := x + 1;
  B:
    x := x + 1;
    y := FALSE;
end algorithm; *)
====
"""

def test_pluscal1():
    with open("/tmp/pluscal.tla", "w") as f:
        f.write(pluscal1)
    tla.pluscal_translate("/tmp/pluscal.tla")
    mod = tla.Module.of_file("/tmp/pluscal.tla")
    assert mod.name == "pluscal"
    assert set(mod.variables) == {"x", "y", "pc"}
    assert set(mod.definitions.keys()) == {"vars", "Init","A", "B", "Terminating", "Spec", "Termination", "Next"}
    assert mod.theorems == []
    x, y, pc = smt.Int("x"), smt.Bool("y"), smt.String("pc")
    x1, y1, pc1 = smt.Int("x'"), smt.Bool("y'"), smt.String("pc'")
    decls = {"x": x, "y": y, "pc" : pc}
    assert mod.action("A", decls).eq(smt.And(
        pc == smt.StringVal("A"),
        x1 == x + 1,
        pc1 == smt.StringVal("B"),
        y1 == y
    ))
    assert mod.action("B", decls).eq(smt.And(
        pc == smt.StringVal("B"),
        x1 == x + 1,
        y1 == smt.BoolVal(False),
        pc1 == smt.StringVal("Done")
    ))

dups = r"""
---- MODULE duplicates ----
EXTENDS Integers, Sequences, TLC

(*--algorithm dup
  variable seq = <<1, 2, 3, 2>>;
  index = 1;
  seen = {};
  is_unique = TRUE;

begin
  Iterate:
    while index <= Len(seq) do
      if seq[index] \notin seen then
        seen := seen \union {seq[index]};
      else
        is_unique := FALSE;
      end if;
      index := index + 1;
    end while;
end algorithm; *)

(*
Iterate == /\ pc = "Iterate"
           /\ IF index <= Len(seq)
                 THEN /\ IF seq[index] \notin seen
                            THEN /\ seen' = (seen \union {seq[index]})
                                 /\ UNCHANGED is_unique
                            ELSE /\ is_unique' = FALSE
                                 /\ seen' = seen
                      /\ index' = index + 1
                      /\ pc' = "Iterate"
                 ELSE /\ pc' = "Done"
                      /\ UNCHANGED << index, seen, is_unique >>
           /\ seq' = seq
*)
====

"""
def test_duplicates():
    with open("/tmp/duplicates.tla", "w") as f:
        f.write(dups)
    tla.pluscal_translate("/tmp/duplicates.tla")
    mod = tla.Module.of_file("/tmp/duplicates.tla")
    assert mod.name == "duplicates"
    assert set(mod.variables) == {"seq", "index", "seen", "is_unique", "pc"}
    assert set(mod.definitions.keys()) == {"vars", "Init","Iterate", "Terminating", "Spec", "Termination", "Next"}
    assert mod.theorems == []

    decls = {
        "seq": smt.Const("seq", smt.SeqSort(smt.IntSort())),
        "index": smt.Int("index"),
        "seen": smt.Const("seen", smt.SetSort(smt.IntSort())),
        "is_unique": smt.Bool("is_unique"),
        "pc": smt.String("pc")
    }
    iterate = mod.action("Iterate", {k: d.decl() for k,d in decls.items()})
    a,b,c = iterate.children()
    assert a.eq(decls["pc"] == smt.StringVal("Iterate"))
    assert c.eq(tla.prime(decls["seq"]) == decls["seq"])
    a,b,c = b.children()
    assert a.eq(decls["index"] <= smt.Length(decls["seq"]))
    assert c.eq(smt.And(
    tla.prime(decls["pc"]) == smt.StringVal("Done"),
    smt.And(
        tla.prime(decls["index"]) == decls["index"],
        tla.prime(decls["seen"]) == decls["seen"],
        tla.prime(decls["is_unique"]) == decls["is_unique"]
    )
    ))



alice_bob = r"""
---- MODULE wire -----

EXTENDS Integers

(*--algorithm wire
  variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5],


define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;


process Wire \in 1..2
    variables 
        sender = "alice",
        receiver = "bob",
        amount \in 1..acc[sender];
begin
    Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposit:
        acc[receiver] := acc[receiver] + amount;
end process;

end algorithm;*)


====================
"""

def test_wire():
    with open("/tmp/wire.tla", "w") as f:
        f.write(alice_bob)
    mod = tla.Module.of_file("/tmp/wire.tla", pcal=True)
    amount = smt.Array("amount", smt.IntSort(), smt.IntSort())
    mod.declare_vars([amount])
    mod.infer_sorts()
    assert mod.name == "wire"
    assert set(mod.variables) == {"people", "acc", "sender", "receiver", "amount", "pc"}
    assert set(mod.definitions.keys()) == {"vars", "Init","NoOverdrafts", "Terminating", "Spec", "Termination", "Next", "Deposit", "Withdraw", "ProcSet", "Wire"}
    assert mod.theorems == []

    p = smt.Const("p", smt.StringSort())
    people = smt.Const("people", smt.SetSort(smt.StringSort()))
    acc = smt.Const("acc", smt.ArraySort(smt.StringSort(), smt.IntSort()))
    people[p]
    acc[p]
    assert mod.action("NoOverdrafts", {
        "people": people,
        "acc": acc
    }).eq(smt.ForAll(p, people[p], acc[p] >= smt.IntVal(0)))




    #decls = mod.infer_sorts(typeok="Init")
    #mod.operator()


