import SatinStress.U1.Certificate.F.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem trace_dep_1 :
    (relation [(trace1,1)]).denote = 0 :=
  Raw.spends traceRow_all (by decide +kernel)

theorem trace_dep_2 :
    (relation [(trace2,1)]).denote = 0 :=
  Raw.spends traceRow_all (by decide +kernel)

theorem trace_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsTracePiv 1 [] colsTrace := by
  unfold colsTrace
  refine Earlier.dep (by decide) (kill K _ 1 [] (by decide) ?_ (of_rel trace_dep_1)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [] (by decide) ?_ (of_rel trace_dep_2)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.F
