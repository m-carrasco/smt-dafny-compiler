; RUN: %SDC compile model --output-dir %T-out/ --input-smt2-model %S/model.smt --input-smt2-method %s --input-smt2-function %s
; RUN: %dafny verify --allow-warnings --standard-libraries %T-out/compiled.dfy | %FileCheck --check-prefix=CHECK-BUILD %s

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (bvuge x y))
(assert (bvuge (bvudiv x y) (_ bv10 32)))
(check-sat)