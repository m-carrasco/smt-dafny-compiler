; RUN: %SLOT -s %s -pall -o %t.slot.smt2
; RUN: %SDC --input-smt2-function %t.slot.smt2 --input-smt2-method %s --output-dir %T-out/
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: %model-packer %s %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN: %model-packer --negate %s %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; CHECK-BUILD: Dafny program verifier finished with 2 verified, 0 errors
; CHECK-SAT: sat: true
; CHECK-UNSAT: sat: false

(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (bvuge x y))
(assert (bvuge (bvudiv x y) (_ bv10 32)))
(check-sat)