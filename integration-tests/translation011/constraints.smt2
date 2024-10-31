; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: %model-packer %s %t.packed.sat
; RUN: %t.build/constraints %t.packed.sat | %FileCheck --check-prefix=CHECK-SAT %s

; RUN: %model-packer --negate %s %t.packed.unsat
; RUN: %t.build/constraints %t.packed.unsat | %FileCheck --check-prefix=CHECK-UNSAT %s

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors
; CHECK-SAT: sat: true
; CHECK-UNSAT: sat: false

; 0x00	0x01	0x00	Modulo of zero by a positive number is zero.
; 0x00	0xFF	0x00	Modulo of zero by a negative number is zero.
; 0x7F	0x01	0x00	Max positive dividend by 1 results in 0.
; 0x80	0xFF	0x00	Min negative dividend by -1 results in 0.
; 0x7F	0x02	0x01	Max positive by 2, remainder is 1.
; 0x80	0x02	0xFE	Min negative dividend by 2, remainder is -2.
; 0x80	0x81	0x00	Min negative by itself gives 0.
; 0x7F	0xFF	0x7F	Positive by -1 returns the dividend itself.
; 0x80	0x7F	0x01	Negative by max positive returns 1.
; 0x01	0x02	0x01	Small positive dividend by 2, result is the dividend.
; 0xFF	0x7F	0xFF	-1 modulo max positive returns -1.
; 0xFF	0x80	0xFF	-1 modulo min negative returns -1.
; 0x80	0x01	0x00	Min negative divided by 1 gives remainder 0.
; 0x7F	0x80	0x7F	Positive by min negative returns dividend.
; 0x81	0x01	0x00	-127 divided by 1 gives 0.
; 0x81	0xFF	0x81	-127 by -1 returns -127 (no remainder).
; 0x02	0xFF	0x02	2 modulo -1 is 2 (no remainder).
; 0x80	0x00	0x80	Division by zero case, typically undefined, return the dividend.

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(assert (= (bvsmod x y) z))
(check-sat)
