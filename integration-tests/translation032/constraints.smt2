; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN:
; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Test Case 1: Equal bit-vectors
(assert (= (bvcomp (_ bv12 4) (_ bv12 4)) (_ bv1 1))) ; Expected: 1 (true)

; Test Case 2: Equal bit-vectors
(assert (= (bvcomp (_ bv15 4) (_ bv15 4)) (_ bv1 1))) ; Expected: 1 (true)

; Test Case 3: Unequal bit-vectors
(assert (= (bvcomp (_ bv12 4) (_ bv10 4)) (_ bv0 1))) ; Expected: 0 (false)

; Test Case 4: Unequal bit-vectors
(assert (= (bvcomp (_ bv1 4) (_ bv2 4)) (_ bv0 1))) ; Expected: 0 (false)

; Check satisfiability
(check-sat)