import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def wRows : List (Probe (FPol × Axis)) := [
  (((), 0), 194)]
def wMinor : List (List GI) := [
  [⟨0, 1⟩]]

theorem W_table :
    sample wRows (pick colsWPiv 1 colsW) = wMinor := by
  rw [pick_W]
  decide +kernel

def wSelect : List (List GI) := [
  [⟨0, -1⟩]]
lemma W_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsWPiv 1 colsW).length =>
      denote ((pick colsWPiv 1 colsW).get i)) :=
  Raw.verified K _ _ W_table wSelect (by decide +kernel)

end SatinStress.U1.Certificate.F
