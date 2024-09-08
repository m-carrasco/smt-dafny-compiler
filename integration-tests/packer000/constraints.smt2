; RUN: %SDC --input-smt2-function %s --input-smt2-method %s --output-dir %T-out/
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: %packer --value 1 5 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN: %packer --value 4294967296 5 --output %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; CHECK-BUILD: Dafny program verifier finished with 1 verified, 0 errors
; CHECK-SAT: variable x: 1
; CHECK-SAT: sat: true
; CHECK-UNSAT: variable x: 4294967296
; CHECK-UNSAT: sat: false

(declare-fun x () (_ BitVec 33))
(assert (= x (_ bv1 33)))
(check-sat)