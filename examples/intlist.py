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

print("=" * 70)
print("All proofs completed successfully!")
print("=" * 70)
