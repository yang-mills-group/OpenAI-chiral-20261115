import SatinStress.U1.Certificate.F.Data
import SatinStress.U1.Certificate.F.GradU
import SatinStress.U1.Certificate.F.LandsU
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.F
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem double_dep_13 :
    (relation [(double13,1), (double1, -1), (double6, 1)]).denote = 0 := by
  let y := relation [(double13,1), (double1, -1), (double6, 1)]
  have hG := congr_arg (divV ℂ frequency (pol:=FPol)) grad_dep_15
  have hL := congr_arg (gradW ℂ frequency (pol:=FPol)) lands_dep_2
  simp only [relation_step, denote_plus, denote_times, relation_nil, denote_zero, map_add, map_zsmul, map_zero] at hG hL
  simp only [grad12, grad5, grad15, luGT ℂ frequency, closed] at hG
  simp only [lands1, lands2, d1, luDiv ℂ frequency] at hL
  change y.denote = 0
  apply (smul_right_injective (M:=Grid (FPol × Axis × Axis)) (show (-1 : ℤ) ≠ 0 by decide))
  simp only [smul_zero]
  have h : ( (-1 : ℤ) • y.denote) = 0 := by
    dsimp only [y]
    simp only [relation_step, denote_plus, denote_times,relation_nil,denote_zero,double1, double6, double13, luGW ℂ frequency, luV ℂ frequency]
    -- difference of linear images of the two earlier relations; `module` to reorder
    -- code computes related combination hG-hL
    linear_combination (norm := module) hG - hL
  exact h

theorem double_dep_14 :
    (relation [(double14,1), (double1, 2), (double2, -1), (double3, -1), (double4, 1), (double9, 1), (double12, 1)]).denote = 0 := by
  let y := relation [(double14,1), (double1, 2), (double2, -1), (double3, -1), (double4, 1), (double9, 1), (double12, 1)]
  have hG := congr_arg (divV ℂ frequency (pol:=FPol)) grad_dep_16
  have hL := congr_arg (gradW ℂ frequency (pol:=FPol)) lands_dep_3
  simp only [relation_step, denote_plus, denote_times, relation_nil, denote_zero, map_add, map_zsmul, map_zero] at hG hL
  simp only [grad1, grad2, grad3, grad8, grad11, grad13, grad16, luGT ℂ frequency, closed] at hG
  simp only [lands1, lands3, d2, luDiv ℂ frequency] at hL
  change y.denote = 0
  apply (smul_right_injective (M:=Grid (FPol × Axis × Axis)) (show (-1 : ℤ) ≠ 0 by decide))
  simp only [smul_zero]
  have h : ( (-1 : ℤ) • y.denote) = 0 := by
    dsimp only [y]
    simp only [relation_step, denote_plus, denote_times,relation_nil,denote_zero,double1, double2, double3, double4, double9, double12, double14, luGW ℂ frequency, luV ℂ frequency]
    -- difference of linear images of the two earlier relations; `module` to reorder
    -- code computes related combination hG-hL
    linear_combination (norm := module) hG - hL
  exact h

theorem double_upper (K : Type*) [Field K] [Algebra K ℂ] [CharZero K] : Earlier K colsDoublePiv 1 [] colsDouble := by
  unfold colsDouble
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
  refine Earlier.dep (by decide) (kill K _ 1 [(double1,-1), (double6,1)] (by decide) ?_ (of_rel double_dep_13)) ?_
  · simp
  refine Earlier.dep (by decide) (kill K _ 1 [(double1,2), (double2,-1), (double3,-1), (double4,1), (double9,1), (double12,1)] (by decide) ?_ (of_rel double_dep_14)) ?_
  · simp
  refine Earlier.piv (by decide) ?_
  exact Earlier.nil ..

end SatinStress.U1.Certificate.F
