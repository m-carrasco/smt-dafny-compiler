; COM: QF_BV/bench_ab/a100test0001.smt2

; RUN: %SDC compile pointwise --output-dir %t.out/ --input-smt2-function %s  --input-smt2-method %s 
; RUN: %dafny verify --allow-warnings --standard-libraries %t.out/compiled.dfy | %FileCheck --check-prefix=CHECK-BUILD %s
; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (bvslt a (_ bv100 32)))
(check-sat)
(exit)