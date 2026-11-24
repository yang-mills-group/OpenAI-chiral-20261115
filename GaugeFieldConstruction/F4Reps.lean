import GaugeFieldConstruction.Coverage
/-! U1 f4: Orbit certificate over raw labels -/
set_option autoImplicit false
open Function
open scoped BigOperators
namespace YM.GaugeFieldConstruction.Certificate
open Raw
-- Lex least (m,o), order in stress manuscript.

def f4T : List (F4 × Sym) :=
  [((0,.inl 0),(S 0 0)),
   ((0,.inl 0),(S 1 1)),
   ((0,.inl 1),(S 0 1))]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f4T : Approves f4Act symAct f4T sTest f4Elems = true := by decide +kernel

theorem f4T_ok : Picked (f4Act.tensorProd symAct) f4T := certify _ _ _ _ _ sTest_ok mem_f4 (paid_f4T)

def f4W : List (F4 × Axis) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f4W : Approves f4Act v f4W wTest f4Elems = true := by decide +kernel

theorem f4W_ok : Picked (f4Act.tensorProd v) f4W := certify _ _ _ _ _ wTest_ok mem_f4 (paid_f4W)

def f4V : List (F4 × VS) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f4V : Approves f4Act vsAct f4V vTest f4Elems = true := by decide +kernel

theorem f4V_ok : Picked (f4Act.tensorProd vsAct) f4V := certify _ _ _ _ _ vTest_ok mem_f4 (paid_f4V)
end YM.GaugeFieldConstruction.Certificate
