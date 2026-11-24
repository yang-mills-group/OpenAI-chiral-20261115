import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def vRows : List (Probe (FPol × VSy)) := [
  (((), (0,Duo.sym 1 2)), 2),
  (((), (0,Duo.sym 1 2)), 4162),
  (((), (0,Duo.sym 0 1)), 4226),
  (((), (0,Duo.sym 1 1)), 4226),
  (((), (0,Duo.sym 0 0)), 194),
  (((), (0,Duo.sym 1 1)), 194),
  (((), (0,Duo.sym 0 1)), 194),
  (((), (0,Duo.sym 0 1)), 8258),
  (((), (0,Duo.sym 1 1)), 8258),
  (((), (0,Duo.sym 1 2)), 262145),
  (((), (0,Duo.sym 0 1)), 17043521),
  (((), (0,Duo.sym 1 1)), 17043521),
  (((), (0,Duo.sym 1 2)), 130),
  (((), (0,Duo.sym 1 2)), 262273)]
def vMinor : List (List GI) := [
  [⟨-1, 0⟩, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨2, 0⟩, 0, 0, ⟨-1, 0⟩, ⟨1, 0⟩],
  [⟨1, 0⟩, ⟨-4, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨-2, 0⟩, 0, 0, ⟨1, 0⟩, 0],
  [0, 0, ⟨2, 0⟩, 0, 0, 0, 0, ⟨2, 0⟩, 0, 0, ⟨-2, 0⟩, 0, 0, 0],
  [0, 0, 0, ⟨0, 2⟩, 0, 0, 0, 0, ⟨0, -2⟩, 0, 0, ⟨0, -2⟩, 0, 0],
  [0, 0, 0, 0, ⟨0, 1⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, ⟨0, 2⟩, 0, ⟨0, 1⟩, 0, 0, ⟨0, 1⟩, 0, 0, 0, 0, 0],
  [0, 0, ⟨2, 0⟩, 0, 0, 0, ⟨-1, 0⟩, ⟨-1, 0⟩, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, ⟨1, 0⟩, ⟨-1, 0⟩, 0, 0, ⟨-2, 0⟩, 0, 0, 0],
  [0, 0, 0, 0, 0, ⟨0, -1⟩, 0, 0, ⟨0, 1⟩, 0, 0, ⟨0, -2⟩, 0, 0],
  [⟨-1, 0⟩, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨-2, 0⟩, 0, 0, ⟨-1, 0⟩, ⟨-1, 0⟩],
  [0, 0, 0, 0, 0, 0, ⟨1, 0⟩, ⟨-1, 0⟩, 0, 0, ⟨2, 0⟩, 0, 0, 0],
  [0, 0, 0, 0, 0, ⟨0, -1⟩, 0, 0, ⟨0, 1⟩, 0, 0, ⟨0, 2⟩, 0, 0],
  [0, ⟨-2, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨2, 0⟩, 0],
  [0, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨2, 0⟩, ⟨1, 0⟩]]
private theorem vRead_1 :
    sample vRows [v1, v2, v3] = [[⟨-1, 0⟩, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨2, 0⟩, 0, 0, ⟨-1, 0⟩, ⟨1, 0⟩], [⟨1, 0⟩, ⟨-4, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨-2, 0⟩, 0, 0, ⟨1, 0⟩, 0], [0, 0, ⟨2, 0⟩, 0, 0, 0, 0, ⟨2, 0⟩, 0, 0, ⟨-2, 0⟩, 0, 0, 0]] := by decide +kernel
private theorem vRead_4 :
    sample vRows [v4, v5, v6] = [[0, 0, 0, ⟨0, 2⟩, 0, 0, 0, 0, ⟨0, -2⟩, 0, 0, ⟨0, -2⟩, 0, 0], [0, 0, 0, 0, ⟨0, 1⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, ⟨0, 2⟩, 0, ⟨0, 1⟩, 0, 0, ⟨0, 1⟩, 0, 0, 0, 0, 0]] := by decide +kernel
private theorem vRead_7 :
    sample vRows [v7, v8, v9] = [[0, 0, ⟨2, 0⟩, 0, 0, 0, ⟨-1, 0⟩, ⟨-1, 0⟩, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, ⟨1, 0⟩, ⟨-1, 0⟩, 0, 0, ⟨-2, 0⟩, 0, 0, 0], [0, 0, 0, 0, 0, ⟨0, -1⟩, 0, 0, ⟨0, 1⟩, 0, 0, ⟨0, -2⟩, 0, 0]] := by decide +kernel
private theorem vRead_13 :
    sample vRows [v13, v14, v15] = [[⟨-1, 0⟩, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨-2, 0⟩, 0, 0, ⟨-1, 0⟩, ⟨-1, 0⟩], [0, 0, 0, 0, 0, 0, ⟨1, 0⟩, ⟨-1, 0⟩, 0, 0, ⟨2, 0⟩, 0, 0, 0], [0, 0, 0, 0, 0, ⟨0, -1⟩, 0, 0, ⟨0, 1⟩, 0, 0, ⟨0, 2⟩, 0, 0]] := by decide +kernel
private theorem vRead_24 :
    sample vRows [v24, v26] = [[0, ⟨-2, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨2, 0⟩, 0], [0, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨2, 0⟩, ⟨1, 0⟩]] := by decide +kernel

theorem V_table :
    sample vRows (pick colsVPiv 1 colsV) = vMinor := by
  rw [pick_V]
  exact (join_readings vRows vRead_1 (join_readings vRows vRead_4 (join_readings vRows vRead_7 (join_readings vRows vRead_13 vRead_24))))

def vSelect : List (List GI) := [
  [⟨-3, 0⟩, ⟨-1, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨-1, 0⟩, ⟨3, 0⟩],
  [0, ⟨-2, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨-3, 0⟩, 0, 0, ⟨-2, 0⟩, ⟨6, 0⟩],
  [0, 0, ⟨1, 0⟩, 0, 0, 0, ⟨1, 0⟩, ⟨1, 0⟩, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, ⟨0, -1⟩, 0, ⟨0, 1⟩, 0, 0, ⟨0, 1⟩, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, ⟨0, -1⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, ⟨0, -1⟩, 0, ⟨0, -1⟩, 0, 0, ⟨0, -1⟩, 0, 0, 0, 0, 0],
  [0, 0, ⟨1, 0⟩, 0, 0, 0, ⟨-1, 0⟩, ⟨-1, 0⟩, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, ⟨1, 0⟩, ⟨-1, 0⟩, 0, 0, ⟨-1, 0⟩, 0, 0, 0],
  [0, 0, 0, 0, 0, ⟨0, 1⟩, 0, 0, ⟨0, -1⟩, 0, 0, ⟨0, 1⟩, 0, 0],
  [⟨-2, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, ⟨-1, 0⟩, 0, 0, 0, 0],
  [0, 0, ⟨1, 0⟩, 0, 0, 0, ⟨2, 0⟩, 0, 0, 0, ⟨1, 0⟩, 0, 0, 0],
  [0, 0, 0, ⟨0, -1⟩, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, ⟨0, -1⟩, 0, 0],
  [⟨-6, 0⟩, ⟨-2, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨3, 0⟩, 0, 0, ⟨4, 0⟩, ⟨-6, 0⟩],
  [0, ⟨2, 0⟩, 0, 0, 0, 0, 0, 0, 0, ⟨-3, 0⟩, 0, 0, ⟨2, 0⟩, ⟨6, 0⟩]]
lemma V_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsVPiv 1 colsV).length =>
      denote ((pick colsVPiv 1 colsV).get i)) :=
  Raw.verified K _ _ V_table vSelect (by decide +kernel)

end SatinStress.U1.Certificate.F
