; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN %model-packer %s %t.packed.sat
; RUN %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN %model-packer --negate %s %t.packed.unsat
; RUN %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; Test with pathological cases

;Signed: Most negative by -1 (Unspecified)
; RUN: %packer --value 128 1 --value 255 1 --value 128 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;Signed: Dividing by 0 (Unspecified)
; RUN: %packer --value 249 1 --value 0 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;Signed: Dividing by 0 (Unspecified)
; RUN: %packer --value 1 1 --value 0 1 --value 255 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;Signed: Most negative by 1
; RUN: %packer --value 128 1 --value 1 1 --value 128 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;Signed: Negative by positive
; RUN: %packer --value 249 1 --value 3 1 --value 254 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;Signed: Positive by negative
; RUN: %packer --value 7 1 --value 253 1 --value 254 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; Signed: Positive by positive
; RUN: %packer --value 10 1 --value 3 1 --value 3 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors
; CHECK-SAT: sat: true
; CHECK-UNSAT: sat: false

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (= (bvsdiv x y) z))
(check-sat)
