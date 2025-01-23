; RUN: %SLOT -s %s -pall -o %t.slot.smt2
; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %t.slot.smt2 --input-smt2-method %s &> %t.sdc.log
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs &> %t.dafnybuild.log
; RUN: cat %t.dafnybuild.log | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: %model-packer %s %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN: %model-packer --negate %s %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors
; CHECK-SAT: sat: true
; CHECK-UNSAT: sat: false

(declare-fun symbolicInt () (_ BitVec 8))
(assert (bvsge symbolicInt (_ bv0 8)))
(check-sat)