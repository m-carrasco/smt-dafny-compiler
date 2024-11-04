; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Shift a 4-bit bit-vector 0xC (1100) right by 1 position
; Expected result: 0x6 (0110 in binary)
(assert (= (bvlshr (_ bv12 4) (_ bv1 4)) (_ bv6 4)))

; Test Case 2: Shift a 4-bit bit-vector 0xF (1111) right by 2 positions
; Expected result: 0x3 (0011 in binary)
(assert (= (bvlshr (_ bv15 4) (_ bv2 4)) (_ bv3 4)))

; Test Case 3: Shift an 8-bit bit-vector 0x90 (10010000) right by 3 positions
; Expected result: 0x12 (00010010 in binary)
(assert (= (bvlshr (_ bv144 8) (_ bv3 8)) (_ bv18 8)))

; Test Case 4: Shift a 6-bit bit-vector 0x3C (111100) right by 4 positions
; Expected result: 0x3 (000011 in binary)
(assert (= (bvlshr (_ bv60 6) (_ bv4 6)) (_ bv3 6)))

; Test Case 5: Shift a 5-bit bit-vector 0x10 (10000) right by 4 positions
; Expected result: 0x1 (00001 in binary)
(assert (= (bvlshr (_ bv16 5) (_ bv4 5)) (_ bv1 5)))

; Check satisfiability
(check-sat)