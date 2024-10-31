; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Assert that (bvsub #b0011 #b0001) should equal #b0010 (3 - 1 = 2)
(assert (= (bvsub #b0011 #b0001) #b0010))

; Assert that (bvsub #b0101 #b0011) should equal #b0010 (5 - 3 = 2)
(assert (= (bvsub #b0101 #b0011) #b0010))

; Assert that (bvsub #b1111 #b0001) should equal #b1110 (15 - 1 = 14)
(assert (= (bvsub #b1111 #b0001) #b1110))

; Assert that (bvsub #b1001 #b0010) should equal #b0111 (9 - 2 = 7)
(assert (= (bvsub #b1001 #b0010) #b0111))

; Assert that (bvsub #b0010 #b0010) should equal #b0000 (2 - 2 = 0)
(assert (= (bvsub #b0010 #b0010) #b0000))

; Assert that (bvsub #b0000 #b0001) should equal #b1111 (0 - 1 = -1, in 4-bit two's complement this is #b1111)
(assert (= (bvsub #b0000 #b0001) #b1111))

; Check satisfiability to verify all assertions hold
(check-sat)