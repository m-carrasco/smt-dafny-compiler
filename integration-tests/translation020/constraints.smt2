; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Concatenate two 8-bit bit-vectors
; 0x12 (00010010) and 0x34 (00110100) to form a 16-bit bit-vector
; Expected result: 0x1234
(assert (= (concat #x12 #x34) #x1234))

; Test Case 2: Concatenate an 8-bit and a 16-bit bit-vector
; 0x56 (01010110) and 0x789A (0111100010011010) to form a 24-bit bit-vector
; Expected result: 0x56789A
(assert (= (concat #x56 #x789A) #x56789A))

; Test Case 3: Concatenate three 4-bit bit-vectors
; 0xA (1010), 0xB (1011), and 0xC (1100) to form a 12-bit bit-vector
; Expected result: 0xABC (101010111100 in binary)
(assert (= (concat (_ bv10 4) (_ bv11 4) (_ bv12 4)) #xABC))

; Test Case 4: Concatenate a 16-bit and an 8-bit bit-vector
; 0x1234 (0001001000110100) and 0xFF (11111111) to form a 24-bit bit-vector
; Expected result: 0x1234FF
(assert (= (concat #x1234 #xFF) #x1234FF))

; Test Case 5: Concatenate a 1-bit, a 2-bit, and a 3-bit bit-vector
; 0b1 (1), 0b10 (10), and 0b011 (011) to form a 6-bit bit-vector
; Expected result: 0b110011 (binary 110011, which is 51 in decimal)
(assert (= (concat (_ bv1 1) (_ bv2 2) (_ bv3 3)) (_ bv51 6)))

; Check satisfiability
(check-sat)
