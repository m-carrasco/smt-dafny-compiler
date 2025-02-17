; COM: QF_BV/dwp_formulas/try5_small_true_functions_dwp_yes.close_stdout_set_file_name.il.dwp.smt2

; RUN: %SLOT -s %s -pall -o %t.slot.smt2
; RUN: %SDC compile pointwise --output-dir %t.out/ --input-smt2-function %s --input-smt2-method %t.slot.smt2 
; RUN: %dafny build --allow-warnings --standard-libraries %t.out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s
; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; RUN: %model-packer %s %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; COM: %model-packer --negate %s %t.packed.unsat
; COM: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s
; CHECK-UNSAT: sat: false

(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Ivan Jager <aij+nospam@andrew.cmu.edu>

|)
(set-info :category "industrial")
(set-info :status sat)
(assert (= (_ bv1 1) (bvand (bvnot (_ bv0 1)) (bvand (_ bv1 1) (_ bv1 1)))))
(check-sat)
(exit)
