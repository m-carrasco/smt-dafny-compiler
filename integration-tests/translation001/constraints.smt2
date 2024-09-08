; RUN: %SDC --input-smt2-function %s --input-smt2-method %s --output-dir %T-out/
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: %model-packer %s %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN: %model-packer --negate %s %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; CHECK-BUILD: Dafny program verifier finished with 1 verified, 0 errors
; CHECK-SAT: sat: true
; CHECK-UNSAT: sat: false

(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (= x y))
(check-sat)