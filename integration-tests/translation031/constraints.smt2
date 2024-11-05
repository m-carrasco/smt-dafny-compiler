; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN:
; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case: Checking equality of bit-vectors
; 15 (0x0F in hexadecimal) should be equal to itself
(assert (= (_ bv15 8) (_ bv15 8))) ; 15 == 15 should evaluate to true

; Additionally, let's test a positive and a negative case
; 15 should not be equal to -15
; -15 in two's complement for 8 bits is 0xF1
(assert (not (= (_ bv15 8) (_ bv241 8)))) ; 15 != -15

; Check satisfiability
(check-sat)