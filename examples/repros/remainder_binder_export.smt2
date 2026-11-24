; Original failed straddle witness conversion while unifying derivatives.
; Linux x86_64/Python 3.12.12/Z3 5.3.3, timeout=1000 ms; source parent be342fd.
; Exported after the failed check; fresh replay solves quickly.
(set-option :timeout 1000)
(declare-fun absR (Real) Real)
(declare-fun t!1835 () Real)
(declare-fun eps!1836 () Real)
(declare-fun k!1834 () Real)
(declare-fun F!1833 () (Array Real Real))
(assert (exists ((delta Real))
  (let ((a!1 (forall ((x Real))
               (let ((a!1 (<= delta (absR (+ x (* (- 1.0) t!1835)))))
                     (a!2 (+ (select F!1833 x)
                             (* (- 1.0) (select F!1833 t!1835))
                             (* (- 1.0) k!1834 (+ x (* (- 1.0) t!1835)))))
                     (a!3 (* (/ 1.0 2.0)
                             eps!1836
                             (absR (+ x (* (- 1.0) t!1835))))))
                 (or a!1 (<= (absR a!2) a!3))))))
    (and (not (<= delta 0.0)) a!1))))
(assert (not (<= eps!1836 0.0)))
(assert (let ((a!1 (exists ((delta Real))
             (let ((a!1 (forall ((y Real))
                          (let ((a!1 (<= delta (absR (+ y (* (- 1.0) t!1835)))))
                                (a!2 (+ (select F!1833 y)
                                        (* (- 1.0) (select F!1833 t!1835))
                                        (* (- 1.0)
                                           k!1834
                                           (+ y (* (- 1.0) t!1835)))))
                                (a!3 (* (/ 1.0 2.0)
                                        eps!1836
                                        (absR (+ y (* (- 1.0) t!1835))))))
                            (or a!1 (<= (absR a!2) a!3))))))
               (and (not (<= delta 0.0)) a!1)))))
  (not a!1)))

(check-sat)
