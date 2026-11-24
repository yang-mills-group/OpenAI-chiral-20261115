import SatinStress.U1.Certificate.X.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.X
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def dRows : List (Probe (XPol × Axis)) := []
def dMinor : List (List GI) := []

theorem D_table :
    sample dRows (pick colsDPiv 1 colsD) = dMinor := by
  rw [pick_D]
  decide +kernel

def dSelect : List (List GI) := []
lemma D_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsDPiv 1 colsD).length =>
      denote ((pick colsDPiv 1 colsD).get i)) :=
  Raw.verified K _ _ D_table dSelect (by decide +kernel)

end SatinStress.U1.Certificate.X
