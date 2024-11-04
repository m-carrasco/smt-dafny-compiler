; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Shift a 4-bit bit-vector 0x3 (0011) left by 1 position
; Expected result: 0x6 (0110 in binary)
(assert (= (bvshl (_ bv3 4) (_ bv1 4)) (_ bv6 4)))

; Test Case 2: Shift a 4-bit bit-vector 0x7 (0111) left by 2 positions
; Expected result: 0xC (1100 in binary)
(assert (= (bvshl (_ bv7 4) (_ bv2 4)) (_ bv12 4)))

; Test Case 3: Shift an 8-bit bit-vector 0x12 (00010010) left by 3 positions
; Expected result: 0x90 (10010000 in binary)
(assert (= (bvshl (_ bv18 8) (_ bv3 8)) (_ bv144 8)))

; Test Case 4: Shift a 6-bit bit-vector 0x1B (011011) left by 2 positions
; Expected result: 0x6C (1101100 in binary, truncated to 6 bits as 101100)
(assert (= (bvshl (_ bv27 6) (_ bv2 6)) (_ bv44 6)))

; Test Case 5: Shift a 5-bit bit-vector 0x1 (00001) left by 4 positions
; Expected result: 0x10 (10000 in binary)
(assert (= (bvshl (_ bv1 5) (_ bv4 5)) (_ bv16 5)))

; Check satisfiability
(check-sat)