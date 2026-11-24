; Unsat. With smt.random_seed 1 z3 returns unknown (timeout), with seed 2
; unknown (incomplete quantifiers); seeds 0 and 3-6 answer unsat in milliseconds.
; Replacing the lambda by an array constant Rle with (forall x y. Rle[x,y] = le x y)
; makes every seed unsat at once.
(set-option :smt.random_seed 1)
(set-option :timeout 10000)
(declare-sort S 0)
(declare-fun mem (S S) Bool)
(declare-fun le (S S) Bool)
(declare-fun is_least ((Array S S Bool) S S) Bool)
(declare-const E S)
(assert (exists ((k S)) (and (mem k E) (forall ((m S)) (=> (mem m E) (le k m))))))
(assert (forall ((R (Array S S Bool)) (E S) (a S))
  (! (= (is_least R E a) (and (mem a E) (forall ((x S)) (=> (mem x E) (select R a x)))))
     :pattern ((is_least R E a)))))
(assert (not (exists ((a S)) (is_least (lambda ((x S) (y S)) (le x y)) E a))))
(check-sat)
(get-info :reason-unknown)
