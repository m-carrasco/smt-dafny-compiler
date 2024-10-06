; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Division by zero
(assert (= (bvurem #b00000001 #b00000000) #b00000001))
(assert (= (bvurem #b11111111 #b00000000) #b11111111))
; Zero divided by any value should be zero
 (assert (= (bvurem #b00000000 #b00000001) #b00000000))
 (assert (= (bvurem #b00000000 #b11111111) #b00000000))
; Dividend smaller than divisor
(assert (= (bvurem #b00001000 #b11111111) #b00001000)) ; 8 % 255 = 8
(assert (= (bvurem #b01111111 #b10000000) #b01111111)) ; 127 % 128 = 127
; Any value mod 1 is zero
(assert (= (bvurem #b00000001 #b00000001) #b00000000)) ; 1 % 1 = 0
(assert (= (bvurem #b11111111 #b00000001) #b00000000)) ; 255 % 1 = 0
; Modulo the maximum value
(assert (= (bvurem #b11111110 #b11111111) #b11111110)) ; 254 % 255 = 254
(assert (= (bvurem #b11111111 #b11111111) #b00000000)) ; 255 % 255 = 0
(assert (= (bvurem #b00000010 #b11111111) #b00000010)) ; 2 % 255 = 2
; Modulo powers of 2
(assert (= (bvurem #b11111111 #b00000100) #b00000011)) ; 255 % 4 = 3
(assert (= (bvurem #b10101010 #b00001000) #b00000010)) ; 170 % 8 = 2
; Max dividend with various divisors
(assert (= (bvurem #b11111111 #b00000010) #b00000001)) ; 255 % 2 = 1
(assert (= (bvurem #b11111111 #b00000101) #b00000000)) ; 255 % 5 = 1