import SatinStress.U1.Certificate.X.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.X
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem lands_upper (K : Type*) [Field K] [Algebra K ℂ] : Earlier K colsLandsPiv 1 [] colsLands := by
  unfold colsLands
  refine Earlier.piv (by decide) ?_
  exact Earlier.nil ..

end SatinStress.U1.Certificate.X
