; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test case 1: Extract the most significant byte from the bit-vector (_ bv4660 16) which is 0x1234
(assert (= ((_ extract 15 8) (_ bv4660 16)) (_ bv18 8)))

; Test case 2: Extract the least significant byte from the bit-vector (_ bv4660 16) which is 0x1234
(assert (= ((_ extract 7 0) (_ bv4660 16)) (_ bv52 8)))

; Test case 3: Extract the single most significant bit from the bit-vector (_ bv32768 16) which is 0x8000
(assert (= ((_ extract 15 15) (_ bv32768 16)) (_ bv1 1)))

; Test case 4: Extract the single least significant bit from the bit-vector (_ bv32768 16) which is 0x8000
(assert (= ((_ extract 0 0) (_ bv32768 16)) (_ bv0 1)))

; Test case 5: Extract bits 7 to 4 from the bit-vector (_ bv4660 16) which is 0x1234
(assert (= ((_ extract 7 4) (_ bv4660 16)) (_ bv3 4)))

; Test case 6: Extract bits 11 to 8 from the bit-vector (_ bv0 16) which is 0x0000
(assert (= ((_ extract 11 8) (_ bv0 16)) (_ bv0 4)))

; Test case 7: Extract all bits (15 down to 0) from the bit-vector (_ bv65535 16) which is 0xFFFF
(assert (= ((_ extract 15 0) (_ bv65535 16)) (_ bv65535 16)))

; Test case 8: Extract bits 14 to 7 from the bit-vector (_ bv12345 16) which is 0x3039
(assert (= ((_ extract 14 7) (_ bv12345 16)) (_ bv96 8)))

; Test case 9: Extract bits 3 to 0 from the bit-vector (_ bv43981 16) which is 0xABCD
(assert (= ((_ extract 3 0) (_ bv43981 16)) (_ bv13 4)))

; Test case 10: Extract bits 15 to 12 from the bit-vector (_ bv61455 16) which is 0xF00F
(assert (= ((_ extract 15 12) (_ bv61455 16)) (_ bv15 4)))

(check-sat)
