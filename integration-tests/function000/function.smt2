; RUN: %SDC compile function --output-dir %T-out/ --input-smt2-function %s --output-function-name "Precondition"
; RUN: %dafny verify --allow-warnings --standard-libraries %T-out/compiled.dfy 
; RUN: cat %T-out/compiled.dfy | %FileCheck --check-prefix=CHECK-DAFNY %s

; CHECK-DAFNY: function Precondition

(set-info :status unknown)
(declare-fun sym2 () (_ BitVec 32))
(declare-fun sym1 () (_ BitVec 32))
(assert
 (let (($x8 (= sym2 sym1)))
 (and $x8 (and (bvult sym1 (_ bv2147483647 32)) (bvult sym2 (_ bv2147483647 32))))))
(check-sat)
