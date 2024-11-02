; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Rotate the constant 0x0000000f (00000000000000000000000000001111) left by 4 bits
; Expected result: 0x000000f0 (00000000000000000000000011110000)
(assert (= ((_ rotate_left 4) #x0000000f) #x000000f0))

; Rotate the constant 0x0000000f left by 8 bits
; Expected result: 0x00000f00 (00000000000000000000111100000000)
(assert (= ((_ rotate_left 8) #x0000000f) #x00000f00))

; Rotate the constant 0x0000000f left by 12 bits
; Expected result: 0x0000f000 (00000000000000001111000000000000)
(assert (= ((_ rotate_left 12) #x0000000f) #x0000f000))

; Rotate the constant 0x0000000f left by 16 bits
; Expected result: 0x000f0000 (00000000000011110000000000000000)
(assert (= ((_ rotate_left 16) #x0000000f) #x000f0000))

; Rotate the constant 0x0000000f left by 28 bits
; Expected result: 0xf0000000 (11110000000000000000000000000000)
(assert (= ((_ rotate_left 28) #x0000000f) #xf0000000))

; Check satisfiability
(check-sat)