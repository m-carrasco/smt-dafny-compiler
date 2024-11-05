; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN:
; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Arithmetic shift right on a positive 8-bit bit-vector
; 0x2A (00101010) shifted right by 2 bits should yield 0x0A (00001010)
(assert (= (bvashr (_ bv42 8) (_ bv2 8)) (_ bv10 8))) ; 42 in decimal is 0x2A, shifted result is 0x0A

; Test Case 2: Arithmetic shift right on a negative 8-bit bit-vector
; 0xD6 (11010110, which is -42 in two's complement) shifted right by 2 bits should yield 0xF5 (11110101)
(assert (= (bvashr (_ bv214 8) (_ bv2 8)) (_ bv245 8))) ; 214 is 0xD6, result is 0xF5 (245 in decimal) ---> FAILS

; Test Case 3: Arithmetic shift right on an 8-bit vector shifted by 0 bits (no change)
; 0x3C (00111100) shifted right by 0 bits should yield 0x3C (00111100)
(assert (= (bvashr (_ bv60 8) (_ bv0 8)) (_ bv60 8))) ; 60 in decimal is 0x3C, no shift should give same result

; Test Case 4: Shift an 8-bit vector by more than its length (should replicate MSB entirely)
; 0x83 (10000011) shifted right by 8 bits should yield 0xFF (11111111)
(assert (= (bvashr (_ bv131 8) (_ bv8 8)) (_ bv255 8))) ; 131 is 0x83, result with full shift is 0xFF (255) ---> FAILS

; Test Case 5: Arithmetic shift right on an 8-bit mixed-sign bit-vector by 1 bit
; 0x7F (01111111) shifted right by 1 bit should yield 0x3F (00111111)
(assert (= (bvashr (_ bv127 8) (_ bv1 8)) (_ bv63 8))) ; 127 in decimal is 0x7F, result is 0x3F (63 in decimal)

; Check satisfiability
(check-sat)
