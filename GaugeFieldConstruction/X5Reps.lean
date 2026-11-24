import GaugeFieldConstruction.Coverage
/-! U1 x5: Orbit certificate over raw labels -/
set_option autoImplicit false
open Function
open scoped BigOperators
namespace YM.GaugeFieldConstruction.Certificate
open Raw
-- Lex least (m,o), order in stress manuscript.

def x5W : List (X5 × Axis) :=
  [((0,(W 0 1)),1)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_x5W : Approves x5Act v x5W wTest x5Elems = true := by decide +kernel

theorem x5W_ok : Picked (x5Act.tensorProd v) x5W := certify _ _ _ _ _ wTest_ok mem_x5 (paid_x5W)

def x5V : List (X5 × VS) :=
  [((0,(W 0 1)),(0,(S 0 1))),
   ((0,(W 0 1)),(1,(S 0 0))),
   ((0,(W 0 1)),(1,(S 1 1))),
   ((0,(W 0 1)),(1,(S 2 2))),
   ((0,(W 0 1)),(2,(S 1 2))),
   ((0,(W 1 2)),(1,(S 0 2)))]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_x5V : Approves x5Act vsAct x5V vTest x5Elems = true := by decide +kernel

theorem x5V_ok : Picked (x5Act.tensorProd vsAct) x5V := certify _ _ _ _ _ vTest_ok mem_x5 (paid_x5V)
end YM.GaugeFieldConstruction.Certificate
