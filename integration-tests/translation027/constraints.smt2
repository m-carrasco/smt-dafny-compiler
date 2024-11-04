; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: NAND operation on two 4-bit bit-vectors
; 0xA (1010) NAND 0x5 (0101) should yield 0xF (1111)
(assert (= (bvnand (_ bv10 4) (_ bv5 4)) (_ bv15 4)))

; Test Case 2: NAND operation on two 4-bit bit-vectors
; 0x0 (0000) NAND 0xF (1111) should yield 0xF (1111)
(assert (= (bvnand (_ bv0 4) (_ bv15 4)) (_ bv15 4)))

; Test Case 3: NAND operation on two 8-bit bit-vectors
; 0x55 (01010101) NAND 0xAA (10101010) should yield 0xFF (11111111)
(assert (= (bvnand (_ bv85 8) (_ bv170 8)) (_ bv255 8))) ; 0xFF is 255 in decimal

; Check satisfiability
(check-sat)
