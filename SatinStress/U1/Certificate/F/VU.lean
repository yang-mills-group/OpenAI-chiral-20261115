import SatinStress.U1.Certificate.F.VParts1
import SatinStress.U1.Certificate.F.VParts2
import SatinStress.U1.Certificate.F.VParts3
import SatinStress.U1.Certificate.F.VParts4

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem V_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsVPiv 1 [] colsV := by
  unfold colsV
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(v5,1)] (by decide) ?_ (of_rel V_dep_10)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v6,1), (v9,1)] (by decide) ?_ (of_rel V_dep_11)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v7,1), (v8,1)] (by decide) ?_ (of_rel V_dep_12)) ?_
  · simp
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(v5,1)] (by decide) ?_ (of_rel V_dep_16)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v6,1), (v15,1)] (by decide) ?_ (of_rel V_dep_17)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v7,1), (v14,1)] (by decide) ?_ (of_rel V_dep_18)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v5,1)] (by decide) ?_ (of_rel V_dep_19)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v4,-1), (v15,-1)] (by decide) ?_ (of_rel V_dep_20)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v4,1), (v6,1), (v15,1)] (by decide) ?_ (of_rel V_dep_21)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v3,-1), (v14,-1)] (by decide) ?_ (of_rel V_dep_22)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v3,1), (v7,1), (v14,1)] (by decide) ?_ (of_rel V_dep_23)) ?_
  · simp
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(v1,1), (v2,1), (v24,-1)] (by decide) ?_ (of_rel V_dep_25)) ?_
  · simp
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(v13,1), (v24,-1), (v26,1)] (by decide) ?_ (of_rel V_dep_27)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v3,-1), (v8,1), (v14,-1)] (by decide) ?_ (of_rel V_dep_28)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(v4,-1), (v9,1), (v15,-1)] (by decide) ?_ (of_rel V_dep_29)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.F
