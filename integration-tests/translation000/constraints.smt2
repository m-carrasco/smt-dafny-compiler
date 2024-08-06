; RUN: %SDC --input-smt2 %s --output-dir %T-out/

(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (bvuge x y))
(assert (bvuge (bvudiv x y) (_ bv10 32)))
(check-sat)