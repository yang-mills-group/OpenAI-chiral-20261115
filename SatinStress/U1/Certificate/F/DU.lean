import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem D_dep_2 :
    (relation [(d2,1), (d1, 2)]).denote = 0 :=
  Raw.spends wRow_all (by decide +kernel)

theorem D_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsDPiv 1 [] colsD := by
  unfold colsD
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(d1,2)] (by decide) ?_ (of_rel D_dep_2)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.F
