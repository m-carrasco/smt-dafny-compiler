; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN:
; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Both operands positive
; 15 % 4 should yield 3
(assert (= (bvsrem (_ bv15 8) (_ bv4 8)) (_ bv3 8))) ; 15 % 4 = 3

; Test Case 2: First operand negative, second operand positive
; -15 % 4 should yield -3
; -15 in two's complement for 8 bits is 0xF1
; -3 in two's complement for 8 bits is 0xFD
(assert (= (bvsrem (_ bv241 8) (_ bv4 8)) (_ bv253 8))) ; -15 % 4 = -3

; Test Case 3: First operand positive, second operand negative
; 15 % -4 should yield 3
; -4 in two's complement for 8 bits is 0xFC
(assert (= (bvsrem (_ bv15 8) (_ bv252 8)) (_ bv3 8))) ; 15 % -4 = 3

; Test Case 4: Both operands negative
; -15 % -4 should yield -3
; -15 in two's complement for 8 bits is 0xF1
; -3 in two's complement for 8 bits is 0xFD
(assert (= (bvsrem (_ bv241 8) (_ bv252 8)) (_ bv253 8))) ; -15 % -4 = -3

; Check satisfiability
(check-sat)