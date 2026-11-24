import GaugeFieldConstruction.Coverage
/-! U1 g5: Orbit certificate over raw labels -/
set_option autoImplicit false
open Function
open scoped BigOperators
namespace YM.GaugeFieldConstruction.Certificate
open Raw
-- Lex least (m,o), order in stress manuscript.

def g5W : List (G5 × Axis) :=
  [(((W 0 1),((W 0 1),0)),0),
   (((W 0 1),((W 0 1),2)),2),
   (((W 0 1),((W 0 2),1)),2),
   (((W 0 1),((W 0 2),2)),1)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_g5W : Approves g5Act v g5W wTest g5Elems = true := by decide +kernel

theorem g5W_ok : Picked (g5Act.tensorProd v) g5W := certify _ _ _ _ _ wTest_ok mem_g5 (paid_g5W)

def g5V : List (G5 × VS) :=
  [(((W 0 1),((W 0 1),0)),(0,(S 0 0))),
   (((W 0 1),((W 0 1),0)),(0,(S 1 1))),
   (((W 0 1),((W 0 1),0)),(0,(S 2 2))),
   (((W 0 1),((W 0 1),0)),(1,(S 0 1))),
   (((W 0 1),((W 0 1),0)),(2,(S 0 2))),
   (((W 0 1),((W 0 1),2)),(0,(S 0 2))),
   (((W 0 1),((W 0 1),2)),(2,(S 0 0))),
   (((W 0 1),((W 0 1),2)),(2,(S 2 2))),
   (((W 0 1),((W 0 1),2)),(2,(S 3 3))),
   (((W 0 1),((W 0 1),2)),(3,(S 2 3))),
   (((W 0 1),((W 0 2),0)),(0,(S 1 2))),
   (((W 0 1),((W 0 2),0)),(1,(S 0 2))),
   (((W 0 1),((W 0 2),0)),(2,(S 0 1))),
   (((W 0 1),((W 0 2),1)),(0,(S 0 2))),
   (((W 0 1),((W 0 2),1)),(1,(S 1 2))),
   (((W 0 1),((W 0 2),1)),(2,(S 0 0))),
   (((W 0 1),((W 0 2),1)),(2,(S 1 1))),
   (((W 0 1),((W 0 2),1)),(2,(S 2 2))),
   (((W 0 1),((W 0 2),1)),(2,(S 3 3))),
   (((W 0 1),((W 0 2),1)),(3,(S 2 3))),
   (((W 0 1),((W 0 2),2)),(0,(S 0 1))),
   (((W 0 1),((W 0 2),2)),(1,(S 0 0))),
   (((W 0 1),((W 0 2),2)),(1,(S 1 1))),
   (((W 0 1),((W 0 2),2)),(1,(S 2 2))),
   (((W 0 1),((W 0 2),2)),(1,(S 3 3))),
   (((W 0 1),((W 0 2),2)),(2,(S 1 2))),
   (((W 0 1),((W 0 2),2)),(3,(S 1 3))),
   (((W 0 1),((W 0 2),3)),(1,(S 2 3))),
   (((W 0 1),((W 0 2),3)),(2,(S 1 3))),
   (((W 0 1),((W 0 2),3)),(3,(S 1 2))),
   (((W 0 1),((W 2 3),0)),(2,(S 1 3))),
   (((W 0 1),((W 2 3),2)),(0,(S 1 3)))]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_g5V : Approves g5Act vsAct g5V vTest g5Elems = true := by decide +kernel

theorem g5V_ok : Picked (g5Act.tensorProd vsAct) g5V := certify _ _ _ _ _ vTest_ok mem_g5 (paid_g5V)
end YM.GaugeFieldConstruction.Certificate
