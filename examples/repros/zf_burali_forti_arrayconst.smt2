; benchmark generated from python API
(set-info :status unknown)
(declare-sort ZFSet 0)
(declare-fun |∈| (ZFSet ZFSet) Bool)
(declare-fun bigunion (ZFSet) ZFSet)
(declare-fun sep (ZFSet (Array ZFSet Bool)) ZFSet)
(declare-fun is_ordinal (ZFSet) Bool)
(declare-fun Pord () (Array ZFSet Bool))
(assert (forall ((y ZFSet)) (= (select Pord y) (is_ordinal y))))
(declare-fun C!2327 () ZFSet)
(declare-fun zf.succ (ZFSet) ZFSet)
(assert
 (forall ((x ZFSet) )(! (let ((?x8 Pord
 ))
 (let ((?x9 (sep C!2327 ?x8)))
 (let ((?x10 (bigunion ?x9)))
 (or (not (|∈| x (zf.succ ?x10))) (|∈| x ?x10))))) :qid k!11))
 )
(assert
 (let ((?x17 Pord
 ))
 (let ((?x18 (sep C!2327 ?x17)))
 (let ((?x19 (bigunion ?x18)))
 (let ((?x20 (zf.succ ?x19)))
 (|∈| ?x19 ?x20))))))
(assert
 (forall ((A ZFSet) )(! (or (not (is_ordinal A)) (|∈| A C!2327)) :qid k!14))
 )
(assert
 (forall ((x ZFSet) )(! (let ((?x8 Pord
 ))
 (let ((?x9 (sep C!2327 ?x8)))
 (let (($x7 (is_ordinal x)))
 (or $x7 (not (|∈| x ?x9)))))) :qid k!17))
 )
(assert
 (let ((?x17 Pord
 ))
 (let ((?x18 (sep C!2327 ?x17)))
 (let ((?x19 (bigunion ?x18)))
 (let ((?x20 (zf.succ ?x19)))
 (is_ordinal ?x20))))))
(assert
 (let ((?x17 Pord
))
(let ((?x18 (sep C!2327 ?x17)))
(let ((?x19 (bigunion ?x18)))
(not (|∈| ?x19 ?x19))))))
(check-sat)
