; RUN: %SDC compile function --output-dir %T-out/ --input-smt2-function %s --output-function-name "Precondition"
; RUN: %dafny verify --allow-warnings --standard-libraries %T-out/compiled.dfy 
; RUN: cat %T-out/compiled.dfy | %FileCheck --check-prefix=CHECK-DAFNY %s

; CHECK-DAFNY: function Precondition

(declare-fun in0 () (_ BitVec 8))
(declare-fun in1 () (_ BitVec 8))
(assert (= in0 in0))
(assert (= in1 in1))
(assert
(let (($x7 (= in1 in0)))
(and $x7 (bvsgt (bvor in1 in0) (_ bv255 8)))))
(check-sat)


