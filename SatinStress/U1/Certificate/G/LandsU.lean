import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem lands_dep_3 :
    (relation [(lands3,1), (lands1, -2)]).denote = 0 :=
  Raw.spends wRow_all (by decide +kernel)

theorem lands_dep_4 :
    (relation [(lands4,1), (lands2, -2)]).denote = 0 :=
  Raw.spends wRow_all (by decide +kernel)

theorem lands_dep_5 :
    (relation [(lands5,1), (lands1, 1), (lands2, -1)]).denote = 0 :=
  Raw.spends wRow_all (by decide +kernel)

theorem lands_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsLandsPiv 1 [] colsLands := by
  unfold colsLands
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(lands1,-2)] (by decide) ?_ (of_rel lands_dep_3)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(lands2,-2)] (by decide) ?_ (of_rel lands_dep_4)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(lands1,1), (lands2,-1)] (by decide) ?_ (of_rel lands_dep_5)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.G
