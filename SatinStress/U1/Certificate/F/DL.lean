import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def dRows : List (Probe (FPol × Axis)) := [
  (((), 0), 194)]
def dMinor : List (List GI) := [
  [⟨0, 1⟩]]

theorem D_table :
    sample dRows (pick colsDPiv 1 colsD) = dMinor := by
  rw [pick_D]
  decide +kernel

def dSelect : List (List GI) := [
  [⟨0, -1⟩]]
lemma D_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsDPiv 1 colsD).length =>
      denote ((pick colsDPiv 1 colsD).get i)) :=
  Raw.verified K _ _ D_table dSelect (by decide +kernel)

end SatinStress.U1.Certificate.F
