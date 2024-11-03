; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Zero-extend a 4-bit bit-vector to 8 bits
; 0xA (1010) zero-extended by 4 bits should become 0x0A (00001010)
(assert (= ((_ zero_extend 4) (_ bv10 4)) (_ bv10 8)))  ; #x0A is equivalent to (_ bv10 8)

; Test Case 2: Zero-extend an 8-bit bit-vector to 16 bits
; 0x12 (00010010) zero-extended by 8 bits should become 0x0012 (0000000000010010)
(assert (= ((_ zero_extend 8) (_ bv18 8)) (_ bv18 16))) ; #x0012 is equivalent to (_ bv18 16)

; Test Case 3: Zero-extend a 6-bit bit-vector to 12 bits
; 0b110011 (binary 110011) zero-extended by 6 bits should become 0x033 (000000110011)
(assert (= ((_ zero_extend 6) (_ bv51 6)) (_ bv51 12))) ; #x033 is equivalent to (_ bv51 12)

; Test Case 4: Zero-extend a 3-bit bit-vector to 8 bits
; 0b101 (binary 101) zero-extended by 5 bits should become 0x05 (00000101)
(assert (= ((_ zero_extend 5) (_ bv5 3)) (_ bv5 8))) ; #x05 is equivalent to (_ bv5 8)

; Test Case 5: Zero-extend a 1-bit bit-vector to 4 bits
; 0b1 (binary 1) zero-extended by 3 bits should become 0x01 (0001)
(assert (= ((_ zero_extend 3) (_ bv1 1)) (_ bv1 4))) ; #x01 is equivalent to (_ bv1 4)

; Check satisfiability
(check-sat)