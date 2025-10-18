"""
Integer List Theory - A pedagogical example of building a theory in knuckledragger

This example demonstrates:
- Defining an inductive datatype (IntList)
- Defining recursive functions (length, append, reverse)
- Proving properties by induction
- Common proof patterns and tactics
"""

import kdrag as kd
import kdrag.smt as smt

# Define the IntList inductive datatype
IntList = kd.Inductive("IntList")
IntList.declare("Nil")
IntList.declare("Cons", ("head", smt.IntSort()), ("tail", IntList))
IntList = IntList.create()

# Constructors
Nil = IntList.Nil
Cons = IntList.Cons

# Common variables
x, y, z = smt.Ints("x y z")
l, l1, l2, l3 = smt.Consts("l l1 l2 l3", IntList)

# Some example lists
empty = Nil
singleton_1 = Cons(1, Nil)
list_123 = Cons(1, Cons(2, Cons(3, Nil)))

print(f"Example lists:")
print(f"  empty = {empty}")
print(f"  singleton = {singleton_1}")
print(f"  [1,2,3] = {list_123}")
print()

# ============================================================================
# Define length function
# ============================================================================

length = smt.Function("length", IntList, smt.IntSort())
length = kd.define("length", [l], smt.If(l.is_Nil, 0, 1 + length(l.tail)))

# Test length on concrete examples
print("Testing length:")
print(f"  length(empty) = {kd.prove(length(empty) == 0, by=[length.defn])}")
print(f"  length([1,2,3]) = {kd.prove(length(list_123) == 3, by=[length.defn])}")
print()

# ============================================================================
# Prove: length is always non-negative
# ============================================================================

@kd.Theorem(smt.ForAll([l], length(l) >= 0))
def length_nonneg(pf):
    """Length is always non-negative"""
    _l = pf.fix()
    pf.induct(_l)
    # Base case: length(Nil) >= 0
    pf.auto(by=[length.defn])
    # Inductive case: length(Cons(x, tail)) >= 0
    pf.auto(by=[length.defn])

print(f"Proved: {length_nonneg}")
print()

# ============================================================================
# Define append function
# ============================================================================

append = smt.Function("append", IntList, IntList, IntList)
append = kd.define(
    "append",
    [l1, l2],
    smt.If(l1.is_Nil, l2, Cons(l1.head, append(l1.tail, l2)))
)

# Register append with + notation
kd.notation.add.register(IntList, append)

print("Testing append:")
print(f"  Nil ++ [1,2,3] = Cons(1, Cons(2, Cons(3, Nil)))")
append_test = kd.prove(append(Nil, list_123) == list_123, by=[append.defn])
print(f"  Proved: {append_test}")
print()

# ============================================================================
# Prove: append with Nil on the right is identity
# ============================================================================

@kd.Theorem(smt.ForAll([l], append(l, Nil) == l))
def append_nil_r(pf):
    """Appending Nil on the right is identity"""
    _l = pf.fix()
    pf.induct(_l)
    # Base case: append(Nil, Nil) == Nil
    pf.auto(by=[append.defn])
    # Inductive case: append(Cons(x, tail), Nil) == Cons(x, tail)
    # Note: induct generates foralls for constructor fields, use fixes()
    _x, _tail = pf.fixes()
    pf.auto(by=[append.defn])

print(f"Proved: {append_nil_r}")
print()

# ============================================================================
# Prove: length of append is sum of lengths
# ============================================================================

@kd.Theorem(smt.ForAll([l1, l2], length(append(l1, l2)) == length(l1) + length(l2)))
def length_append(pf):
    """Length of appended lists is sum of lengths"""
    _l1, _l2 = pf.fixes()
    pf.induct(_l1)
    # Base case: length(append(Nil, l2)) == length(Nil) + length(l2)
    pf.auto(by=[append.defn, length.defn])
    # Inductive case: length(append(Cons(x, tail), l2)) == length(Cons(x, tail)) + length(l2)
    _x, _tail = pf.fixes()
    pf.auto(by=[append.defn, length.defn])

print(f"Proved: {length_append}")
print()

# ============================================================================
# Prove: append is associative
# ============================================================================

@kd.Theorem(smt.ForAll([l1, l2, l3], append(append(l1, l2), l3) == append(l1, append(l2, l3))))
def append_assoc(pf):
    """Append is associative"""
    _l1, _l2, _l3 = pf.fixes()
    pf.induct(_l1)
    # Base case
    pf.auto(by=[append.defn])
    # Inductive case
    _x, _tail = pf.fixes()
    pf.auto(by=[append.defn])

print(f"Proved: {append_assoc}")
print()

# ============================================================================
# Define reverse function
# ============================================================================

rev = smt.Function("rev", IntList, IntList)
rev = kd.define("rev", [l], smt.If(l.is_Nil, Nil, append(rev(l.tail), Cons(l.head, Nil))))

print("Testing reverse:")
rev_test = kd.prove(rev(Cons(1, Cons(2, Cons(3, Nil)))) == Cons(3, Cons(2, Cons(1, Nil))), by=[rev.defn, append.defn])
print(f"  rev([1,2,3]) = [3,2,1]")
print(f"  Proved: {rev_test}")
print()

# ============================================================================
# Prove: reverse of reverse is identity
# ============================================================================

# First we need a helper lemma about reverse and append
@kd.Theorem(smt.ForAll([l1, l2], rev(append(l1, l2)) == append(rev(l2), rev(l1))))
def rev_append(pf):
    """Reverse distributes over append (with order swap)"""
    _l1, _l2 = pf.fixes()
    pf.induct(_l1)
    # Base case: rev(append(Nil, l2)) == append(rev(l2), rev(Nil))
    # Need append_nil_r to simplify append(rev(l2), Nil)
    pf.auto(by=[append.defn, rev.defn, append_nil_r])
    # Inductive case
    _x, _tail = pf.fixes()
    pf.auto(by=[append.defn, rev.defn, append_assoc])

print(f"Proved helper lemma: {rev_append}")
print()

@kd.Theorem(smt.ForAll([l], rev(rev(l)) == l))
def rev_rev(pf):
    """Reverse of reverse is identity"""
    _l = pf.fix()
    pf.induct(_l)
    # Base case: rev(rev(Nil)) == Nil
    pf.auto(by=[rev.defn])
    # Inductive case: rev(rev(Cons(x, tail))) == Cons(x, tail)
    _x, _tail = pf.fixes()
    pf.auto(by=[rev.defn, rev_append, append.defn])

print(f"Proved: {rev_rev}")
print()

# ============================================================================
# Define membership predicate
# ============================================================================

mem = smt.Function("mem", smt.IntSort(), IntList, smt.BoolSort())
mem = kd.define("mem", [x, l], smt.If(l.is_Nil, False, smt.Or(l.head == x, mem(x, l.tail))))

print("Testing membership:")
mem_test1 = kd.prove(mem(2, list_123) == True, by=[mem.defn])
mem_test2 = kd.prove(mem(5, list_123) == False, by=[mem.defn])
print(f"  2 ∈ [1,2,3]: {mem_test1}")
print(f"  5 ∈ [1,2,3]: {mem_test2}")
print()

# ============================================================================
# Prove: membership in append (Lean/Rocq tactic style)
# ============================================================================

@kd.Theorem(smt.ForAll([x, l1, l2], mem(x, append(l1, l2)) == smt.Or(mem(x, l1), mem(x, l2))))
def mem_append_tactic(pf):
    """Membership in append - tactic style proof"""
    _x, _l1, _l2 = pf.fixes()
    pf.induct(_l1)
    # Base case: mem(x, append(Nil, l2)) == mem(x, l2)
    pf.auto(by=[append.defn, mem.defn])
    # Inductive case
    _head, _tail = pf.fixes()
    pf.auto(by=[append.defn, mem.defn])

print(f"Proved (tactic style): {mem_append_tactic}")
print()

# ============================================================================
# Prove: membership preserved by append - easier version for Isar style
# ============================================================================

# This one is easier to prove - just use the full characterization
@kd.Theorem(smt.ForAll([x, l1, l2], smt.Implies(mem(x, l1), mem(x, append(l1, l2)))))
def mem_append_left(pf):
    """If x is in l1, then x is in append(l1, l2) - using helper lemma"""
    _x, _l1, _l2 = pf.fixes()
    pf.intros()
    # Just use mem_append_tactic which already proved the equivalence
    pf.show(mem(_x, append(_l1, _l2)), by=[mem_append_tactic])

print(f"Proved: {mem_append_left}")
print()

# ============================================================================
# Length of reverse equals length of original
# ============================================================================

@kd.Theorem(smt.ForAll([l], length(rev(l)) == length(l)))
def length_rev(pf):
    """Length of reverse equals length of original"""
    _l = pf.fix()
    pf.induct(_l)
    # Base case
    pf.auto(by=[rev.defn, length.defn])
    # Inductive case
    _head, _tail = pf.fixes()
    # Need length_append to help
    pf.auto(by=[rev.defn, length.defn, length_append])

print(f"Proved: {length_rev}")
print()

# ============================================================================
# Define map function
# ============================================================================

map_f = smt.Function("map", (smt.IntSort() >> smt.IntSort()), IntList, IntList)
f = smt.Const("f", smt.IntSort() >> smt.IntSort())
map_f = kd.define("map", [f, l], smt.If(l.is_Nil, Nil, Cons(f(l.head), map_f(f, l.tail))))

# Example: map (+1) over a list
succ = smt.Lambda([x], x + 1)
print("Testing map:")
map_test = kd.prove(map_f(succ, Cons(1, Cons(2, Nil))) == Cons(2, Cons(3, Nil)), by=[map_f.defn])
print(f"  map(+1, [1,2]) = [2,3]: {map_test}")
print()

# ============================================================================
# Prove: length of map equals length of original
# ============================================================================

@kd.Theorem(smt.ForAll([f, l], length(map_f(f, l)) == length(l)))
def length_map(pf):
    """Length of map equals length of original"""
    _f, _l = pf.fixes()
    pf.induct(_l)
    # Base case
    pf.auto(by=[map_f.defn, length.defn])
    # Inductive case
    _head, _tail = pf.fixes()
    pf.auto(by=[map_f.defn, length.defn])

print(f"Proved: {length_map}")
print()

# ============================================================================
# Prove: map distributes over append (Isar style)
# ============================================================================

@kd.Theorem(smt.ForAll([f, l1, l2], map_f(f, append(l1, l2)) == append(map_f(f, l1), map_f(f, l2))))
def map_append(pf):
    """Map distributes over append - Isar style with explicit reasoning"""
    _f, _l1, _l2 = pf.fixes()
    pf.induct(_l1)

    # Base case: map(f, append(Nil, l2)) == append(map(f, Nil), map(f, l2))
    pf.have(append(Nil, _l2) == _l2, by=[append.defn])
    pf.have(map_f(_f, Nil) == Nil, by=[map_f.defn])
    pf.have(append(Nil, map_f(_f, _l2)) == map_f(_f, _l2), by=[append.defn])
    pf.show(map_f(_f, append(Nil, _l2)) == append(map_f(_f, Nil), map_f(_f, _l2)), by=[])

    # Inductive case
    _head, _tail = pf.fixes()
    # IH: map(f, append(tail, l2)) == append(map(f, tail), map(f, l2))
    # Show: map(f, append(Cons(h,t), l2)) == append(map(f, Cons(h,t)), map(f, l2))
    pf.auto(by=[append.defn, map_f.defn])

print(f"Proved (Isar style): {map_append}")
print()

# ============================================================================
# Define filter function
# ============================================================================

pred = smt.Const("pred", smt.IntSort() >> smt.BoolSort())
filter_f = smt.Function("filter", (smt.IntSort() >> smt.BoolSort()), IntList, IntList)
filter_f = kd.define(
    "filter",
    [pred, l],
    smt.If(
        l.is_Nil,
        Nil,
        smt.If(pred(l.head), Cons(l.head, filter_f(pred, l.tail)), filter_f(pred, l.tail))
    )
)

# Example: filter positive numbers
is_pos = smt.Lambda([x], x > 0)
print("Testing filter:")
filter_test = kd.prove(
    filter_f(is_pos, Cons(-1, Cons(2, Cons(-3, Cons(4, Nil))))) == Cons(2, Cons(4, Nil)),
    by=[filter_f.defn]
)
print(f"  filter(>0, [-1,2,-3,4]) = [2,4]: {filter_test}")
print()

# ============================================================================
# Prove: length of filter is at most length of original
# ============================================================================

@kd.Theorem(smt.ForAll([pred, l], length(filter_f(pred, l)) <= length(l)))
def length_filter(pf):
    """Length of filtered list is at most length of original"""
    _pred, _l = pf.fixes()
    pf.induct(_l)
    # Base case
    pf.auto(by=[filter_f.defn, length.defn])
    # Inductive case
    _head, _tail = pf.fixes()
    # Two sub-cases: pred(head) is true or false
    # Z3 should handle the case split automatically
    pf.auto(by=[filter_f.defn, length.defn])

print(f"Proved: {length_filter}")
print()

# ============================================================================
# Define sum function
# ============================================================================

sum_f = smt.Function("sum", IntList, smt.IntSort())
sum_f = kd.define("sum", [l], smt.If(l.is_Nil, 0, l.head + sum_f(l.tail)))

print("Testing sum:")
sum_test = kd.prove(sum_f(list_123) == 6, by=[sum_f.defn])
print(f"  sum([1,2,3]) = 6: {sum_test}")
print()

# ============================================================================
# Prove: sum of append is sum of parts (Isar style with careful steps)
# ============================================================================

@kd.Theorem(smt.ForAll([l1, l2], sum_f(append(l1, l2)) == sum_f(l1) + sum_f(l2)))
def sum_append(pf):
    """Sum distributes over append - detailed Isar style proof"""
    _l1, _l2 = pf.fixes()
    pf.induct(_l1)

    # Base case: sum(append(Nil, l2)) == sum(Nil) + sum(l2)
    pf.have(append(Nil, _l2) == _l2, by=[append.defn])
    pf.have(sum_f(Nil) == 0, by=[sum_f.defn])
    pf.have(0 + sum_f(_l2) == sum_f(_l2), by=[])
    # Now the goal has implications from the have statements
    # We need to discharge them all with auto
    pf.auto(by=[append.defn, sum_f.defn])

    # Inductive case: sum(append(Cons(h,t), l2)) == sum(Cons(h,t)) + sum(l2)
    _head, _tail = pf.fixes()
    # IH: sum(append(tail, l2)) == sum(tail) + sum(l2)
    pf.have(append(Cons(_head, _tail), _l2) == Cons(_head, append(_tail, _l2)), by=[append.defn])
    pf.have(sum_f(Cons(_head, _tail)) == _head + sum_f(_tail), by=[sum_f.defn])
    # sum(append(Cons(h,t), l2)) = sum(Cons(h, append(t, l2))) = h + sum(append(t, l2))
    #                             = h + (sum(t) + sum(l2))      [by IH]
    #                             = (h + sum(t)) + sum(l2)
    #                             = sum(Cons(h,t)) + sum(l2)
    pf.auto(by=[append.defn, sum_f.defn])

print(f"Proved (Isar style): {sum_append}")
print()

# ============================================================================
# Map-sum fusion (advanced property)
# ============================================================================

@kd.Theorem(smt.ForAll([f, l], sum_f(map_f(f, l)) == sum_f(map_f(f, l))))
def map_sum_fusion_trivial(pf):
    """Trivial identity for demonstration"""
    pf.auto()

# More interesting: if we had homomorphism properties
# But for now let's prove something concrete

# Define double function
double_lam = smt.Lambda([x], 2 * x)

@kd.Theorem(smt.ForAll([l], sum_f(map_f(double_lam, l)) == 2 * sum_f(l)))
def sum_map_double(pf):
    """Sum of doubled list is double the sum"""
    _l = pf.fix()
    pf.induct(_l)
    # Base case
    pf.auto(by=[map_f.defn, sum_f.defn])
    # Inductive case
    _head, _tail = pf.fixes()
    pf.auto(by=[map_f.defn, sum_f.defn])

print(f"Proved: {sum_map_double}")
print()

# ============================================================================
# Append is not commutative (for non-empty lists)
# ============================================================================

# We can't prove append IS commutative, but we can show a counterexample exists
# This is more of a sanity check

print("Sanity check: append is NOT commutative")
l1 = Cons(1, Nil)
l2 = Cons(2, Nil)
not_comm = kd.prove(append(l1, l2) != append(l2, l1), by=[append.defn])
print(f"  [1] ++ [2] != [2] ++ [1]: {not_comm}")
print()

print("=" * 70)
print("All proofs completed successfully!")
print(f"Total theorems proved: 15")
print("Styles demonstrated:")
print("  - Tactic style (Lean/Rocq): fix, induct, auto")
print("  - Isar style: have/show with explicit reasoning")
print("=" * 70)
