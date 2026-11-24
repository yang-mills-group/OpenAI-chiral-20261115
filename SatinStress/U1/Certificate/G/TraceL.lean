import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

def traceRows : List (Probe (GPol × Unit)) := [
  (((0, 0), ()), 532482)]
def traceMinor : List (List GI) := [
  [⟨16, 0⟩]]

theorem trace_table :
    sample traceRows (pick colsTracePiv 1 colsTrace) = traceMinor := by
  rw [pick_trace]
  decide +kernel

def traceSelect : List (List GI) := [
  [⟨1, 0⟩]]
lemma trace_lower (K : Type*) [Field K] [Algebra K ℂ] :
    LinearIndependent K (fun i : Fin (pick colsTracePiv 1 colsTrace).length =>
      denote ((pick colsTracePiv 1 colsTrace).get i)) :=
  Raw.verified K _ _ trace_table traceSelect (by decide +kernel)

end SatinStress.U1.Certificate.G
