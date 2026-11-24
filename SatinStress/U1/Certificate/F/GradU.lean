import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem grad_dep_15 :
    (relation [(grad15,1), (grad5, -1), (grad12, -1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem grad_dep_16 :
    (relation [(grad16,1), (grad1, 1), (grad2, 1), (grad3, -1), (grad8, -1), (grad11, -1), (grad13, -1)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem grad_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsGradPiv 1 [] colsGrad := by
  unfold colsGrad
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(grad5,-1), (grad12,-1)] (by decide) ?_ (of_rel grad_dep_15)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(grad1,1), (grad2,1), (grad3,-1), (grad8,-1), (grad11,-1), (grad13,-1)] (by decide) ?_ (of_rel grad_dep_16)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.F
