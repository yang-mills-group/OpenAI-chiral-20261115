import SatinStress.U1.Certificate.X.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.X
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def vRows : List (Probe (XPol × VSy)) := [
  ((0, (0,Duo.sym 0 1)), 281612415664192),
  ((0, (0,Duo.sym 1 1)), 281612415664192),
  ((0, (0,Duo.sym 0 0)), 138512695360),
  ((0, (0,Duo.sym 1 1)), 138512695360),
  ((0, (0,Duo.sym 0 1)), 138512695360),
  ((0, (0,Duo.sym 1 2)), 137438953536)]
def vMinor : List (List GI) := [
  [⟨-2, 0⟩, 0, 0, 0, 0, 0],
  [0, ⟨0, -2⟩, 0, 0, 0, 0],
  [0, 0, ⟨0, 2⟩, 0, 0, 0],
  [0, 0, 0, ⟨0, 2⟩, 0, 0],
  [0, 0, 0, 0, ⟨2, 0⟩, 0],
  [0, 0, 0, 0, 0, ⟨1, 0⟩]]
private theorem vRead_1 :
    sample vRows [v1, v2, v3] = [[⟨-2, 0⟩, 0, 0, 0, 0, 0], [0, ⟨0, -2⟩, 0, 0, 0, 0], [0, 0, ⟨0, 2⟩, 0, 0, 0]] := by decide +kernel
private theorem vRead_4 :
    sample vRows [v4, v5, v6] = [[0, 0, 0, ⟨0, 2⟩, 0, 0], [0, 0, 0, 0, ⟨2, 0⟩, 0], [0, 0, 0, 0, 0, ⟨1, 0⟩]] := by decide +kernel

theorem V_table :
    sample vRows (pick colsVPiv 1 colsV) = vMinor := by
  rw [pick_V]
  exact (join_readings vRows vRead_1 vRead_4)

def vSelect : List (List GI) := [
  [⟨-1, 0⟩, 0, 0, 0, 0, 0],
  [0, ⟨0, 1⟩, 0, 0, 0, 0],
  [0, 0, ⟨0, -1⟩, 0, 0, 0],
  [0, 0, 0, ⟨0, -1⟩, 0, 0],
  [0, 0, 0, 0, ⟨1, 0⟩, 0],
  [0, 0, 0, 0, 0, ⟨1, 0⟩]]
lemma V_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsVPiv 1 colsV).length =>
      denote ((pick colsVPiv 1 colsV).get i)) :=
  Raw.verified K _ _ V_table vSelect (by decide +kernel)

end SatinStress.U1.Certificate.X
