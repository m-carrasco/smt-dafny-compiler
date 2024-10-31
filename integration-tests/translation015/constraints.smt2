; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Assert that (bvmul #b0001 #b0010) should equal #b0010 (1 * 2 = 2)
(assert (= (bvmul #b0001 #b0010) #b0010))

; Assert that (bvmul #b0011 #b0010) should equal #b0110 (3 * 2 = 6)
(assert (= (bvmul #b0011 #b0010) #b0110))

; Assert that (bvmul #b1111 #b0001) should equal #b1111 (15 * 1 = 15)
(assert (= (bvmul #b1111 #b0001) #b1111))

; Assert that (bvmul #b0100 #b0011) should equal #b1100 (4 * 3 = 12)
(assert (= (bvmul #b0100 #b0011) #b1100))

; Assert that (bvmul #b0010 #b0010) should equal #b0100 (2 * 2 = 4)
(assert (= (bvmul #b0010 #b0010) #b0100))

; Assert that (bvmul #b0000 #b1010) should equal #b0000 (0 * 10 = 0)
(assert (= (bvmul #b0000 #b1010) #b0000))

; Check satisfiability to verify all assertions hold
(check-sat)