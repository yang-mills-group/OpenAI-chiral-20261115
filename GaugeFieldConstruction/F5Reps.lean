import GaugeFieldConstruction.Coverage
/-! U1 f5: Orbit certificate over raw labels -/
set_option autoImplicit false
open Function
open scoped BigOperators
namespace YM.GaugeFieldConstruction.Certificate
open Raw
-- Lex least (m,o), order in stress manuscript.

def f5W : List (F5 × Axis) :=
  [((0,.inr (.inr (0,0))),0),
   ((0,.inr (.inr (0,1))),1),
   ((0,.inr (.inr (1,0))),1),
   ((0,.inr (.inr (1,1))),0)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f5W : Approves f5Act v f5W wTest f5Elems = true := by decide +kernel

theorem f5W_ok : Picked (f5Act.tensorProd v) f5W := certify _ _ _ _ _ wTest_ok mem_f5 (paid_f5W)

def f5V : List (F5 × VS) :=
  [((0,.inl (S 0 1)),(2,(S 0 3))),
   ((0,.inl (S 1 1)),(2,(S 1 3))),
   ((0,.inl (S 1 2)),(1,(S 1 3))),
   ((0,.inl (S 1 2)),(3,(S 1 1))),
   ((0,.inr (.inr (0,0))),(0,(S 0 0))),
   ((0,.inr (.inr (0,0))),(0,(S 1 1))),
   ((0,.inr (.inr (0,0))),(1,(S 0 1))),
   ((0,.inr (.inr (0,1))),(0,(S 0 1))),
   ((0,.inr (.inr (0,1))),(1,(S 0 0))),
   ((0,.inr (.inr (0,1))),(1,(S 1 1))),
   ((0,.inr (.inr (0,1))),(1,(S 2 2))),
   ((0,.inr (.inr (0,1))),(2,(S 1 2))),
   ((0,.inr (.inl (S 0 1))),(2,(S 0 3))),
   ((0,.inr (.inr (1,0))),(0,(S 0 1))),
   ((0,.inr (.inr (1,0))),(1,(S 0 0))),
   ((0,.inr (.inr (1,0))),(1,(S 1 1))),
   ((0,.inr (.inr (1,0))),(1,(S 2 2))),
   ((0,.inr (.inr (1,0))),(2,(S 1 2))),
   ((0,.inr (.inr (1,1))),(0,(S 0 0))),
   ((0,.inr (.inr (1,1))),(0,(S 1 1))),
   ((0,.inr (.inr (1,1))),(0,(S 2 2))),
   ((0,.inr (.inr (1,1))),(1,(S 0 1))),
   ((0,.inr (.inr (1,1))),(2,(S 0 2))),
   ((0,.inr (.inr (1,2))),(0,(S 1 2))),
   ((0,.inr (.inr (1,2))),(1,(S 0 2))),
   ((0,.inr (.inr (1,2))),(2,(S 0 1))),
   ((0,.inr (.inl (S 1 1))),(2,(S 1 3))),
   ((0,.inr (.inl (S 1 2))),(1,(S 1 3))),
   ((0,.inr (.inl (S 1 2))),(3,(S 1 1)))]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f5V : Approves f5Act vsAct f5V vTest f5Elems = true := by decide +kernel

theorem f5V_ok : Picked (f5Act.tensorProd vsAct) f5V := certify _ _ _ _ _ vTest_ok mem_f5 (paid_f5V)
end YM.GaugeFieldConstruction.Certificate
