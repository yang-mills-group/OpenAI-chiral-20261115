import GaugeFieldConstruction.Coverage
/-! U1 g4: Orbit certificate over raw labels -/
set_option autoImplicit false
open Function
open scoped BigOperators
namespace YM.GaugeFieldConstruction.Certificate
open Raw
-- Lex least (m,o), order in stress manuscript.

def g4T : List (G4 × Sym) :=
  [((ordered (W 0 1) (W 0 1)),(S 0 0)),
   ((ordered (W 0 1) (W 0 1)),(S 2 2)),
   ((ordered (W 0 1) (W 0 2)),(S 1 2))]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_g4T : Approves g4Act symAct g4T sTest g4Elems = true := by decide +kernel

theorem g4T_ok : Picked (g4Act.tensorProd symAct) g4T := certify _ _ _ _ _ sTest_ok mem_g4 (paid_g4T)

def g4W : List (G4 × Axis) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_g4W : Approves g4Act v g4W wTest g4Elems = true := by decide +kernel

theorem g4W_ok : Picked (g4Act.tensorProd v) g4W := certify _ _ _ _ _ wTest_ok mem_g4 (paid_g4W)

def g4V : List (G4 × VS) :=
  []

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
private lemma paid_g4V : Approves g4Act vsAct g4V vTest g4Elems = true := by decide +kernel

theorem g4V_ok : Picked (g4Act.tensorProd vsAct) g4V := certify _ _ _ _ _ vTest_ok mem_g4 (paid_g4V)
end YM.GaugeFieldConstruction.Certificate
