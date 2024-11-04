; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors
; Test Case 1: NOR operation on two 4-bit bit-vectors
; 0xA (1010) NOR 0x5 (0101) should yield 0x0 (0000)
(assert (= (bvnor (_ bv10 4) (_ bv5 4)) (_ bv0 4)))

; Test Case 2: NOR operation on two 4-bit bit-vectors
; 0x0 (0000) NOR 0xF (1111) should yield 0x0 (0000)
(assert (= (bvnor (_ bv0 4) (_ bv15 4)) (_ bv0 4)))

; Test Case 3: NOR operation on two 8-bit bit-vectors
; 0x55 (01010101) NOR 0xAA (10101010) should yield 0x0 (00000000)
(assert (= (bvnor (_ bv85 8) (_ bv170 8)) (_ bv0 8)))

; Test Case 4: NOR operation on two 6-bit bit-vectors
; 0x3C (111100) NOR 0x03 (000011) should yield 0xC0 (110000)
(assert (= (bvnor (_ bv85 8) (_ bv170 8)) (_ bv0 8))) ; #xC0 truncated to 6 bits is 110000 or (_ bv48 6)

; Test Case 5: NOR operation on two 5-bit bit-vectors
; 0x1C (11100) NOR 0x03 (00011) should yield 0x0 (00000)
(assert (= (bvnor (_ bv28 5) (_ bv3 5)) (_ bv0 5)))

; Check satisfiability
(check-sat)