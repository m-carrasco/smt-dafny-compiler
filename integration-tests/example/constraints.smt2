; RUN: %SLOT -s %s -pall -o %t.slot.smt2
; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %t.slot.smt2 --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

(assert (= (bvlshr x #b00001000) (bvlshr y #b00000001))) 

(check-sat)