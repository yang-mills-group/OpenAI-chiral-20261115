import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def doubleRows : List (Probe (FPol × Axis × Axis)) := [
  (((), (0, 0)), 259),
  (((), (0, 1)), 3),
  (((), (0, 1)), 4291),
  (((), (0, 0)), 266434),
  (((), (0, 1)), 8323),
  (((), (0, 1)), 259),
  (((), (0, 1)), 12355),
  (((), (0, 0)), 3),
  (((), (0, 1)), 17043586),
  (((), (0, 1)), 17047618),
  (((), (0, 1)), 262146),
  (((), (0, 1)), 266434),
  (((), (0, 1)), 270466)]
def doubleMinor : List (List GI) := [
  [⟨-1, 0⟩, 0, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, ⟨0, -1⟩, 0, 0, 0],
  [0, ⟨0, -2⟩, 0, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, ⟨0, 2⟩, ⟨0, -4⟩, ⟨0, 6⟩],
  [0, ⟨0, 2⟩, ⟨0, -2⟩, 0, ⟨0, 10⟩, 0, ⟨0, -2⟩, 0, ⟨0, 4⟩, ⟨0, -4⟩, ⟨0, -2⟩, 0, ⟨0, -2⟩],
  [0, 0, ⟨0, 2⟩, ⟨-4, 0⟩, ⟨0, 4⟩, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, 0],
  [0, 0, ⟨0, 2⟩, 0, ⟨0, -4⟩, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, 0],
  [⟨-1, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, ⟨0, 1⟩, 0, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, ⟨0, 1⟩, 0, 0, 0],
  [⟨-1, 0⟩, 0, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, 0, 0, 0],
  [⟨1, 0⟩, 0, ⟨0, 1⟩, 0, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, ⟨0, -2⟩, ⟨0, -3⟩, 0, 0, 0],
  [0, 0, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, 0, ⟨0, -2⟩, ⟨0, 3⟩, 0, 0, 0],
  [0, ⟨0, -2⟩, 0, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, ⟨0, -6⟩, 0, ⟨0, 2⟩],
  [⟨1, 0⟩, 0, ⟨0, 1⟩, ⟨4, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, ⟨0, 1⟩, 0, 0, 0],
  [0, 0, ⟨0, -6⟩, 0, ⟨0, -4⟩, 0, ⟨0, 2⟩, 0, ⟨0, 4⟩, ⟨0, -4⟩, 0, ⟨0, -4⟩, ⟨0, -4⟩]]
private theorem doubleRead_1 :
    sample doubleRows [double1, double2, double3] = [[⟨-1, 0⟩, 0, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, ⟨0, -1⟩, 0, 0, 0], [0, ⟨0, -2⟩, 0, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, ⟨0, 2⟩, ⟨0, -4⟩, ⟨0, 6⟩], [0, ⟨0, 2⟩, ⟨0, -2⟩, 0, ⟨0, 10⟩, 0, ⟨0, -2⟩, 0, ⟨0, 4⟩, ⟨0, -4⟩, ⟨0, -2⟩, 0, ⟨0, -2⟩]] := by decide +kernel
private theorem doubleRead_4 :
    sample doubleRows [double4, double5, double6] = [[0, 0, ⟨0, 2⟩, ⟨-4, 0⟩, ⟨0, 4⟩, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, 0], [0, 0, ⟨0, 2⟩, 0, ⟨0, -4⟩, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, 0], [⟨-1, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] := by decide +kernel
private theorem doubleRead_7 :
    sample doubleRows [double7, double8, double9] = [[0, 0, ⟨0, 1⟩, 0, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, ⟨0, 1⟩, 0, 0, 0], [⟨-1, 0⟩, 0, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, -1⟩, 0, 0, 0], [⟨1, 0⟩, 0, ⟨0, 1⟩, 0, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, ⟨0, -2⟩, ⟨0, -3⟩, 0, 0, 0]] := by decide +kernel
private theorem doubleRead_10 :
    sample doubleRows [double10, double11, double12] = [[0, 0, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, 0, ⟨0, -2⟩, ⟨0, 3⟩, 0, 0, 0], [0, ⟨0, -2⟩, 0, 0, ⟨0, 2⟩, 0, 0, 0, 0, 0, ⟨0, -6⟩, 0, ⟨0, 2⟩], [⟨1, 0⟩, 0, ⟨0, 1⟩, ⟨4, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, ⟨0, 1⟩, 0, 0, 0]] := by decide +kernel
private theorem doubleRead_15 :
    sample doubleRows [double15] = [[0, 0, ⟨0, -6⟩, 0, ⟨0, -4⟩, 0, ⟨0, 2⟩, 0, ⟨0, 4⟩, ⟨0, -4⟩, 0, ⟨0, -4⟩, ⟨0, -4⟩]] := by decide +kernel

theorem double_table :
    sample doubleRows (pick colsDoublePiv 1 colsDouble) = doubleMinor := by
  rw [pick_double]
  exact (join_readings doubleRows doubleRead_1 (join_readings doubleRows doubleRead_4 (join_readings doubleRows doubleRead_7 (join_readings doubleRows doubleRead_10 doubleRead_15))))

def doubleSelect : List (List GI) := [
  [0, ⟨0, 4⟩, ⟨0, -1⟩, 0, 0, ⟨0, 3⟩, ⟨0, 1⟩, ⟨4, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩],
  [0, ⟨0, -1⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, 1⟩, ⟨0, -1⟩],
  [0, ⟨0, -4⟩, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩],
  [0, ⟨0, 4⟩, ⟨0, -1⟩, 0, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, 0, 0, 0, ⟨0, -1⟩, 0, ⟨0, 2⟩],
  [0, ⟨0, -7⟩, ⟨0, -1⟩, 0, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, 0, 0, 0, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, -2⟩],
  [⟨-8, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨0, -5⟩, ⟨0, -1⟩, 0, ⟨0, 2⟩, 0, 0, ⟨0, 2⟩, ⟨0, 2⟩],
  [0, ⟨0, -3⟩, 0, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨0, -2⟩, ⟨0, 2⟩, 0, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩],
  [0, 0, 0, 0, 0, 0, 0, ⟨-1, 0⟩, 0, 0, 0, 0, 0],
  [0, ⟨0, 1⟩, ⟨0, -1⟩, 0, 0, ⟨0, -1⟩, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, 1⟩],
  [0, ⟨0, -2⟩, ⟨0, -1⟩, 0, 0, ⟨0, 1⟩, ⟨0, 1⟩, 0, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 3⟩, ⟨0, 1⟩],
  [0, ⟨0, 1⟩, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, 1⟩, 0, 0],
  [0, ⟨0, 4⟩, ⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, 0, 0, 0, ⟨0, -1⟩, 0, ⟨0, 2⟩],
  [0, ⟨0, 1⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, 1⟩, ⟨0, 1⟩]]
lemma double_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsDoublePiv 1 colsDouble).length =>
      denote ((pick colsDoublePiv 1 colsDouble).get i)) :=
  Raw.verified K _ _ double_table doubleSelect (by decide +kernel)

end SatinStress.U1.Certificate.F
