import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem grad_dep_21 :
    (relation [(grad21,1), (grad1, -2), (grad2, -2), (grad7, -2)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem grad_dep_22 :
    (relation [(grad22,1), (grad3, -2), (grad8, -2), (grad9, -2)]).denote = 0 :=
  Raw.spends vRow_all (by decide +kernel)

theorem grad_dep_23 :
    (relation [(grad23,1), (grad6, -1), (grad11, -1), (grad14, 1), (grad17, -1), (grad20, -1)]).denote = 0 :=
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
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(grad1,-2), (grad2,-2), (grad7,-2)] (by decide) ?_ (of_rel grad_dep_21)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(grad3,-2), (grad8,-2), (grad9,-2)] (by decide) ?_ (of_rel grad_dep_22)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(grad6,-1), (grad11,-1), (grad14,1), (grad17,-1), (grad20,-1)] (by decide) ?_ (of_rel grad_dep_23)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.G
