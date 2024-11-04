; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Repeat a 2-bit bit-vector 0b01 three times
; Expected result: 0b010101 (6-bit bit-vector)
(assert (= ((_ repeat 3) (_ bv1 2)) (_ bv21 6))) ; 0b010101 is 21 in decimal

; Test Case 2: Repeat a 1-bit bit-vector 0b1 four times
; Expected result: 0b1111 (4-bit bit-vector)
(assert (= ((_ repeat 4) (_ bv1 1)) (_ bv15 4))) ; 0b1111 is 15 in decimal

; Test Case 3: Repeat a 3-bit bit-vector 0b101 two times
; Expected result: 0b101101 (6-bit bit-vector)
(assert (= ((_ repeat 2) (_ bv5 3)) (_ bv45 6))) ; 0b101101 is 45 in decimal

; Test Case 4: Repeat a 4-bit bit-vector 0b1100 three times
; Expected result: 0b110011001100 (12-bit bit-vector)
(assert (= ((_ repeat 3) (_ bv12 4)) (_ bv3276 12))) ; 0b110011001100 is 3276 in decimal

; Test Case 5: Repeat a 2-bit bit-vector 0b10 five times
; Expected result: 0b1010101010 (10-bit bit-vector)
(assert (= ((_ repeat 5) (_ bv2 2)) (_ bv682 10))) ; 0b1010101010 is 682 in decimal

; Check satisfiability
(check-sat)