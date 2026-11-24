import SatinStress.U1.Certificate.X.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.X
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def doubleRows : List (Probe (XPol × Axis × Axis)) := [
  ((0, (0, 0)), 138512695425),
  ((0, (0, 0)), 137438957697),
  ((0, (0, 1)), 281612415664257),
  ((0, (0, 1)), 138512695425),
  ((0, (0, 1)), 138512699457),
  ((0, (0, 0)), 139586699328),
  ((0, (0, 1)), 137438957697)]
def doubleMinor : List (List GI) := [
  [⟨-2, 0⟩, 0, ⟨0, -2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨-2, 0⟩, 0],
  [0, ⟨2, 0⟩, ⟨0, -2⟩, 0, 0, 0, 0],
  [0, 0, ⟨0, -2⟩, 0, 0, 0, 0],
  [⟨-2, 0⟩, 0, 0, 0, 0, ⟨-2, 0⟩, 0],
  [0, 0, 0, ⟨0, 2⟩, ⟨0, -2⟩, 0, 0],
  [⟨2, 0⟩, ⟨-2, 0⟩, 0, ⟨0, 2⟩, ⟨0, 2⟩, ⟨-2, 0⟩, 0],
  [0, 0, 0, 0, ⟨0, 2⟩, 0, ⟨0, -2⟩]]
private theorem doubleRead_1 :
    sample doubleRows [double1, double2, double3] = [[⟨-2, 0⟩, 0, ⟨0, -2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨-2, 0⟩, 0], [0, ⟨2, 0⟩, ⟨0, -2⟩, 0, 0, 0, 0], [0, 0, ⟨0, -2⟩, 0, 0, 0, 0]] := by decide +kernel
private theorem doubleRead_4 :
    sample doubleRows [double4, double5, double6] = [[⟨-2, 0⟩, 0, 0, 0, 0, ⟨-2, 0⟩, 0], [0, 0, 0, ⟨0, 2⟩, ⟨0, -2⟩, 0, 0], [⟨2, 0⟩, ⟨-2, 0⟩, 0, ⟨0, 2⟩, ⟨0, 2⟩, ⟨-2, 0⟩, 0]] := by decide +kernel
private theorem doubleRead_7 :
    sample doubleRows [double7] = [[0, 0, 0, 0, ⟨0, 2⟩, 0, ⟨0, -2⟩]] := by decide +kernel

theorem double_table :
    sample doubleRows (pick colsDoublePiv 1 colsDouble) = doubleMinor := by
  rw [pick_double]
  exact (join_readings doubleRows doubleRead_1 (join_readings doubleRows doubleRead_4 doubleRead_7))

def doubleSelect : List (List GI) := [
  [⟨-1, 0⟩, 0, 0, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩],
  [⟨1, 0⟩, ⟨2, 0⟩, 0, 0, 0, ⟨-1, 0⟩, 0],
  [0, ⟨-2, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, 0, ⟨0, 1⟩],
  [0, 0, 0, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩, ⟨0, 1⟩],
  [0, 0, 0, ⟨0, -1⟩, ⟨0, 1⟩, 0, ⟨0, 1⟩],
  [⟨1, 0⟩, 0, 0, 0, 0, ⟨-1, 0⟩, 0],
  [0, 0, 0, 0, 0, 0, ⟨0, 1⟩]]
lemma double_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsDoublePiv 1 colsDouble).length =>
      denote ((pick colsDoublePiv 1 colsDouble).get i)) :=
  Raw.verified K _ _ double_table doubleSelect (by decide +kernel)

end SatinStress.U1.Certificate.X
