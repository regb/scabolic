(declare-fun x () Int)
(declare-fun y () Int)
(assert (< (+ x y) 3))
(assert (< x y))
(assert (< y x))
(check-sat)
(pop 1)
(check-sat)

