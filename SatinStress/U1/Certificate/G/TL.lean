import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def tRows : List (Probe (GPol × Sy)) := [
  (((0, 0), Duo.sym 0 0), 532482),
  (((0, 1), Duo.sym 0 0), 532482),
  (((0, 1), Duo.sym 0 1), 532482)]
def tMinor : List (List GI) := [
  [⟨4, 0⟩, ⟨4, 0⟩, 0],
  [⟨4, 0⟩, ⟨-4, 0⟩, 0],
  [0, 0, ⟨0, 4⟩]]

theorem T_table :
    sample tRows (pick colsTPiv 1 colsT) = tMinor := by
  rw [pick_T]
  decide +kernel

def tSelect : List (List GI) := [
  [⟨1, 0⟩, ⟨1, 0⟩, 0],
  [⟨1, 0⟩, ⟨-1, 0⟩, 0],
  [0, 0, ⟨0, -1⟩]]
lemma T_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsTPiv 1 colsT).length =>
      denote ((pick colsTPiv 1 colsT).get i)) :=
  Raw.verified K _ _ T_table tSelect (by decide +kernel)

end SatinStress.U1.Certificate.G
