; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: %model-packer %s %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN: %model-packer --negate %s %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; Test with pathological cases

;(0x00 = 0, 0x01 = 1)	0 < 1 (unsigned comparison)	true
; RUN: %packer --value 0x00 1 --value 0x01 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0xFF = -1, 0x00 = 0)	255 < 0 (unsigned comparison)	true
; RUN: %packer --value 0xFF 1 --value 0x00 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x80 = -128, 0x7F = 127)	128 < 127 (unsigned comparison)	true
; RUN: %packer --value 0x80 1 --value 0x7F 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x80 = -128, 0x01 = 1)	128 < 1 (unsigned comparison)	true
; RUN: %packer --value 0x80 1 --value 0x01 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0xFD = -3, 0xFE = -2)	253 < 254 (unsigned comparison)	true
; RUN: %packer --value 0xFD 1 --value 0xFE 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x01 = 1, 0x02 = 2)	1 < 2 (unsigned comparison)	true
; RUN: %packer --value 0x01 1 --value 0x02 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0xFF = -1, 0x7F = 127)	255 < 127 (unsigned comparison)	true
; RUN: %packer --value 0xFF 1 --value 0x7F 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x7E = 126, 0x7F = 127)	126 < 127 (unsigned comparison)	true
; RUN: %packer --value 0x7E 1 --value 0x7F 1 --value 1 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x7F = 127, 0x80 = -128)	127 < 128 (unsigned comparison)	false
; RUN: %packer --value 0x7F 1 --value 0x80 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0xFF = -1, 0xFE = -2)	255 < 254 (unsigned comparison)	false
; RUN: %packer --value 0xFF 1 --value 0xFE 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x80 = -128, 0x80 = -128)	128 < 128 (unsigned comparison)	false
; RUN: %packer --value 0x80 1 --value 0x80 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x01 = 1, 0xFF = -1)	1 < 255 (unsigned comparison)	false
; RUN: %packer --value 0x01 1 --value 0xFF 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x7F = 127, 0xFF = -1)	127 < 255 (unsigned comparison)	false
; RUN: %packer --value 0x7F 1 --value 0xFF 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0x01 = 1, 0x80 = -128)	1 < 128 (unsigned comparison)	false
; RUN: %packer --value 0x01 1 --value 0x80 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

;(0xFE = -2, 0xFD = -3)	    254 < 253 (unsigned comparison)	false
; RUN: %packer --value 0xFE 1 --value 0xFD 1 --value 0 1 --output %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors
; CHECK-SAT: sat: true
; CHECK-UNSAT: sat: false

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () Bool)
(assert (= (bvslt x y) z))
(check-sat)
