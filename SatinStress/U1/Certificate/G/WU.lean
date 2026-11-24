import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem W_dep_3 :
    (relation [(w3,1), (w2, -1)]).denote = 0 :=
  Raw.spends wRow_all (by decide +kernel)

theorem W_dep_4 :
    (relation [(w4,1), (w1, 1)]).denote = 0 :=
  Raw.spends wRow_all (by decide +kernel)

theorem W_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsWPiv 1 [] colsW := by
  unfold colsW
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(w2,-1)] (by decide) ?_ (of_rel W_dep_3)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(w1,1)] (by decide) ?_ (of_rel W_dep_4)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.G
