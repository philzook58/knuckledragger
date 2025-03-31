(declare-const x Int)
(declare-fun axiom (Bool String) Bool)
(declare-fun prove0 (Int Bool) Bool)
(declare-fun prove1 (Int Bool Int) Bool)
(declare-fun prove2 (Int Bool Int Int) Bool)

(assert (prove0 0 (or true false)))
