import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem T_dep_2 :
    (relation [(t2,1), (t1, 1)]).denote = 0 :=
  Raw.spends tRow_all (by decide +kernel)

theorem T_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsTPiv 1 [] colsT := by
  unfold colsT
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(t1,1)] (by decide) ?_ (of_rel T_dep_2)) ?_
  · simp
  refine Earlier.piv (by decide) ?_
  exact Earlier.nil ..

end SatinStress.U1.Certificate.F
