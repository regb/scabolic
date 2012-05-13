(set-logic QF_A)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun v1 () Element)
(declare-fun v2 () Element)

(assert (= i1 i2))
(assert (= (select a i1) v1))
(assert (= (select a i2) v2))
(assert (not (= v1 v2)))

(check-sat)
(exit)
