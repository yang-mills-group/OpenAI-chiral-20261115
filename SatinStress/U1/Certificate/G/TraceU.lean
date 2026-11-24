import SatinStress.U1.Certificate.G.Data

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem trace_dep_2 :
    (relation [(trace2,1), (trace1, -1)]).denote = 0 :=
  Raw.spends traceRow_all (by decide +kernel)

theorem trace_dep_3 :
    (relation [(trace3,1)]).denote = 0 :=
  Raw.spends traceRow_all (by decide +kernel)

theorem trace_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsTracePiv 1 [] colsTrace := by
  unfold colsTrace
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(trace1,-1)] (by decide) ?_ (of_rel trace_dep_2)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [] (by decide) ?_ (of_rel trace_dep_3)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.G
