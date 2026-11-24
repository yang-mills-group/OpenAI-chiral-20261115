import GaugeFieldConstruction.Coverage
/-! U1 f3: Orbit certificate over raw labels -/
set_option autoImplicit false
open Function
open scoped BigOperators
namespace YM.GaugeFieldConstruction.Certificate
open Raw
-- Lex least (m,o), order in stress manuscript.

def f3T : List (F3 × Sym) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f3T : Approves f3Act symAct f3T sTest f3Elems = true := by decide +kernel

theorem f3T_ok : Picked (f3Act.tensorProd symAct) f3T := certify _ _ _ _ _ sTest_ok mem_f3 (paid_f3T)

def f3W : List (F3 × Axis) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f3W : Approves f3Act v f3W wTest f3Elems = true := by decide +kernel

theorem f3W_ok : Picked (f3Act.tensorProd v) f3W := certify _ _ _ _ _ wTest_ok mem_f3 (paid_f3W)

def f3V : List (F3 × VS) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_f3V : Approves f3Act vsAct f3V vTest f3Elems = true := by decide +kernel

theorem f3V_ok : Picked (f3Act.tensorProd vsAct) f3V := certify _ _ _ _ _ vTest_ok mem_f3 (paid_f3V)
end YM.GaugeFieldConstruction.Certificate
