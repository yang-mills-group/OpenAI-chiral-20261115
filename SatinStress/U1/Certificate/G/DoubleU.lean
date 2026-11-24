import SatinStress.U1.Certificate.G.Data
import SatinStress.U1.Certificate.G.GradU
import SatinStress.U1.Certificate.G.LandsU
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

-- This file from the U1 certificate generator (`the construction notes`).
-- Proof by Lean kernel checks; no axiom for evaluation or assumption on the data.
namespace SatinStress.U1.Certificate.G
open Radix Raw Class Derivative

-- high limits only in these arithmetic-certificate files
set_option maxHeartbeats 32000000
set_option maxRecDepth 120000

theorem double_dep_9 :
    (relation [(double9,1), (double1, -1), (double3, 1), (double4, 1)]).denote = 0 := by
  let y := relation [(double9,1), (double1, -1), (double3, 1), (double4, 1)]
  have hG := congr_arg (divV ℂ frequency (pol:=GPol)) grad_dep_21
  have hL := congr_arg (gradW ℂ frequency (pol:=GPol)) lands_dep_3
  simp only [relation_step, denote_plus, denote_times, relation_nil, denote_zero, map_add, map_zsmul, map_zero] at hG hL
  simp only [grad1, grad2, grad7, grad21, luGT ℂ frequency, closed] at hG
  simp only [lands1, lands3, d1, luDiv ℂ frequency] at hL
  change y.denote = 0
  apply (smul_right_injective (M:=Grid (GPol × Axis × Axis)) (show (-2 : ℤ) ≠ 0 by decide))
  simp only [smul_zero]
  have h : ( (-2 : ℤ) • y.denote) = 0 := by
    dsimp only [y]
    simp only [relation_step, denote_plus, denote_times,relation_nil,denote_zero,double1, double3, double4, double9, luGW ℂ frequency, luV ℂ frequency]
    -- difference of linear images of the two earlier relations; `module` to reorder
    -- code computes related combination hG-hL
    linear_combination (norm := module) hG - hL
  exact h

theorem double_dep_11 :
    (relation [(double11,1), (double2, -1), (double5, 1), (double10, 1)]).denote = 0 := by
  let y := relation [(double11,1), (double2, -1), (double5, 1), (double10, 1)]
  have hG := congr_arg (divV ℂ frequency (pol:=GPol)) grad_dep_22
  have hL := congr_arg (gradW ℂ frequency (pol:=GPol)) lands_dep_4
  simp only [relation_step, denote_plus, denote_times, relation_nil, denote_zero, map_add, map_zsmul, map_zero] at hG hL
  simp only [grad3, grad8, grad9, grad22, luGT ℂ frequency, closed] at hG
  simp only [lands2, lands4, d2, luDiv ℂ frequency] at hL
  change y.denote = 0
  apply (smul_right_injective (M:=Grid (GPol × Axis × Axis)) (show (-2 : ℤ) ≠ 0 by decide))
  simp only [smul_zero]
  have h : ( (-2 : ℤ) • y.denote) = 0 := by
    dsimp only [y]
    simp only [relation_step, denote_plus, denote_times,relation_nil,denote_zero,double2, double5, double10, double11, luGW ℂ frequency, luV ℂ frequency]
    -- difference of linear images of the two earlier relations; `module` to reorder
    -- code computes related combination hG-hL
    linear_combination (norm := module) hG - hL
  exact h

theorem double_dep_22 :
    (relation [(double22,1), (double1, 1), (double2, -1), (double8, 1), (double13, 1), (double16, -1), (double19, 1)]).denote = 0 := by
  let y := relation [(double22,1), (double1, 1), (double2, -1), (double8, 1), (double13, 1), (double16, -1), (double19, 1)]
  have hG := congr_arg (divV ℂ frequency (pol:=GPol)) grad_dep_23
  have hL := congr_arg (gradW ℂ frequency (pol:=GPol)) lands_dep_5
  simp only [relation_step, denote_plus, denote_times, relation_nil, denote_zero, map_add, map_zsmul, map_zero] at hG hL
  simp only [grad6, grad11, grad14, grad17, grad20, grad23, luGT ℂ frequency, closed] at hG
  simp only [lands1, lands2, lands5, d3, luDiv ℂ frequency] at hL
  change y.denote = 0
  apply (smul_right_injective (M:=Grid (GPol × Axis × Axis)) (show (-1 : ℤ) ≠ 0 by decide))
  simp only [smul_zero]
  have h : ( (-1 : ℤ) • y.denote) = 0 := by
    dsimp only [y]
    simp only [relation_step, denote_plus, denote_times,relation_nil,denote_zero,double1, double2, double8, double13, double16, double19, double22, luGW ℂ frequency, luV ℂ frequency]
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
  refine Earlier.dep (by decide) (kill K _ 1 [(double1,-1), (double3,1), (double4,1)] (by decide) ?_ (of_rel double_dep_9)) ?_
  · simp
  refine Earlier.piv (by decide) ?_
  refine Earlier.dep (by decide) (kill K _ 1 [(double2,-1), (double5,1), (double10,1)] (by decide) ?_ (of_rel double_dep_11)) ?_
  · simp
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
  refine Earlier.dep (by decide) (kill K _ 1 [(double1,1), (double2,-1), (double8,1), (double13,1), (double16,-1), (double19,1)] (by decide) ?_ (of_rel double_dep_22)) ?_
  · simp
  exact Earlier.nil ..

end SatinStress.U1.Certificate.G
