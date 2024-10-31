; RUN: %SDC compile pointwise --output-dir %T-out/ --input-smt2-function %s --input-smt2-method %s 
; RUN: %dafny build --allow-warnings --standard-libraries %T-out/compiled.dfy -o %t.build/constraints.cs | %FileCheck --check-prefix=CHECK-BUILD %s

; RUN: touch %t
; RUN: %t.build/constraints %t | %FileCheck --check-prefix=CHECK-SAT %s
; CHECK-SAT: sat: true

; CHECK-BUILD: Dafny program verifier finished with [[VERIFIED:[1-9][0-9]*]] verified, 0 errors

; Assert that #b0010 is less than #b0100 (2 < 4)
(assert (bvult #b0010 #b0100))

; Assert that #b0001 is less than #b0011 (1 < 3)
(assert (bvult #b0001 #b0011))

; Assert that #b0110 is less than #b1110 (6 < 14)
(assert (bvult #b0110 #b1110))

; Assert that #b0000 is less than #b1111 (0 < 15)
(assert (bvult #b0000 #b1111))

; Assert that #b0011 is less than #b0101 (3 < 5)
(assert (bvult #b0011 #b0101))

; Test cases where bvult should be false

; Assert that #b1111 is not less than #b1110 (15 >= 14)
(assert (not (bvult #b1111 #b1110)))

; Assert that #b0101 is not less than #b0011 (5 >= 3)
(assert (not (bvult #b0101 #b0011)))

; Assert that #b0010 is not less than #b0010 (2 >= 2, equality case)
(assert (not (bvult #b0010 #b0010)))

; Check satisfiability to verify all assertions hold
(check-sat)