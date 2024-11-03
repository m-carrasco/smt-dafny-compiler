; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Sign-extend a 4-bit bit-vector to 8 bits
; Positive number: 0x7 (0111) extended to 8 bits should remain 0x07 (00000111)
(assert (= ((_ sign_extend 4) (_ bv7 4)) (_ bv7 8)))  ; 0x07 -> 00000111

; Test Case 2: Sign-extend a 4-bit bit-vector to 8 bits
; Negative number: 0xB (1011, which is -5 in signed representation) should extend to 0xFB (11111011)
(assert (= ((_ sign_extend 4) (_ bv11 4)) (_ bv251 8))) ; 0xFB -> 11111011

; Test Case 4: Sign-extend a 3-bit bit-vector to 8 bits
; Negative number: 0b101 (5 in decimal, which is -3 in signed 3-bit) should extend to 0xFD (11111101)
(assert (= ((_ sign_extend 5) (_ bv5 3)) (_ bv253 8))) ; 0xFD -> 11111101

; Test Case 5: Sign-extend a 1-bit bit-vector to 4 bits
; Negative number: 1 (1 in binary, which is -1 in signed 1-bit) should extend to 0xF (1111)
(assert (= ((_ sign_extend 3) (_ bv1 1)) (_ bv15 4))) ; 0xF -> 1111

; Check satisfiability
(check-sat)