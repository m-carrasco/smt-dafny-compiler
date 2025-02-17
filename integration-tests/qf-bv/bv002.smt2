; COM: QF_BV/check2/bvsmod.smt2

; RUN: %SLOT -s %s -pall -o %t.slot.smt2
; RUN: %SDC compile pointwise --output-dir %t.out/ --input-smt2-function %t.slot.smt2 --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %t.out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s
; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; COM: %model-packer %s %t.packed.sat
; COM: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; RUN: %model-packer --negate %s %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s
; CHECK-UNSAT: sat: false

(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test bvsmod edge case
|)
(set-info :category "check")
(set-info :status unsat)
(assert (= (bvsmod (_ bv0 4) (_ bv10 4)) (_ bv10 4)))
(check-sat)
(exit)
