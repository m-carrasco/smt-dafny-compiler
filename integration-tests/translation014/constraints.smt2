; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Assert that (bvor #b0001 #b0010) should equal #b0011
(assert (= (bvor #b0001 #b0010) #b0011))

; Assert that (bvor #b0101 #b0011) should equal #b0111
(assert (= (bvor #b0101 #b0011) #b0111))

; Assert that (bvor #b1111 #b0000) should equal #b1111
(assert (= (bvor #b1111 #b0000) #b1111))

; Assert that (bvor #b1100 #b1010) should equal #b1110
(assert (= (bvor #b1100 #b1010) #b1110))

; Assert that (bvor #b1001 #b0101) should equal #b1101
(assert (= (bvor #b1001 #b0101) #b1101))

; Assert that (bvor #b0000 #b0000) should equal #b0000
(assert (= (bvor #b0000 #b0000) #b0000))

; Check satisfiability to verify all assertions hold
(check-sat)