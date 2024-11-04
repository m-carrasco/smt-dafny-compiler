; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: XNOR operation on two identical 4-bit bit-vectors
; 0xF (1111) XNOR 0xF (1111) should yield 0xF (1111)
(assert (= (bvxnor (_ bv15 4) (_ bv15 4)) (_ bv15 4))) ; 0xF is 15 in decimal

; Test Case 2: XNOR operation on all 1's and all 0's
; 0xF (1111) XNOR 0x0 (0000) should yield 0x0 (0000)
(assert (= (bvxnor (_ bv15 4) (_ bv0 4)) (_ bv0 4))) ; 0x0 is 0 in decimal

; Test Case 3: XNOR operation on two 8-bit bit-vectors
; 0xAA (10101010) XNOR 0x55 (01010101) should yield 0x0 (00000000)
(assert (= (bvxnor (_ bv170 8) (_ bv85 8)) (_ bv0 8))) ; 0x0 is 0 in decimal

; Check satisfiability
(check-sat)