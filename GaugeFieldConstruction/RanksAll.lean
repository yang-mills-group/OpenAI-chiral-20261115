import GaugeFieldConstruction.TotalLevels

/-!
# Totals, finite dimensionality. Full over complex. (Real forms later.)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction
open Calibration Floor Raw U1 Cauchy Row Record Submodule Module Function
namespace Calibration
variable {U V K : Type*} [AddCommGroup U] [AddCommGroup V] [Module ℂ U] [Module ℂ V]
section
private def eq2 (T : Submodule ℂ U) : (Bool → T) ≃ₗ[ℂ] (T × T) where
  toFun f:=(f true,f false)
  invFun u b:=if b then u.1 else u.2
  left_inv x:=by ext1 i; cases i <;> rfl
  right_inv x:= rfl
  map_add' x y:=rfl; map_smul' c y:=rfl

-- solve explicit instances (this tree mixes matrix norms). pure algebra.
private theorem times2 (T : Submodule ℂ U) (h : Module.Finite ℂ T) : finrank ℂ (Bool → T)=
    2*finrank ℂ T := by rw [(eq2 T).finrank_eq,Module.finrank_prod,two_mul]
end
private theorem invoice {α : Type*} (B : Labels α) (d : Floor)
    (p : Module.Finite ℂ (recG.allowed B (SG d)))
    (q : Module.Finite ℂ (ph.allowed B (SF d)))
    (u : Module.Finite ℂ (recX.allowed B (SX d))) : finrank ℂ (invariant B d) =
    finrank ℂ (recG.allowed B (SG d)) + (2*finrank ℂ (ph.allowed B (SF d))+2*finrank ℂ (recX.allowed B (SX d))) := by
  rw [(package d B).finrank_eq]
  haveI := Free.of_divisionRing ℂ ↥(recG.allowed B (SG d))
  haveI := Free.of_divisionRing ℂ (Bool → ↥(ph.allowed B (SF d)))
  haveI := Free.of_divisionRing ℂ (Bool → ↥(recX.allowed B (SX d)))
  haveI := Free.of_divisionRing ℂ ((Bool → ↥(ph.allowed B (SF d))) × (Bool → ↥(recX.allowed B (SX d))))
  unfold Trio; rw [Module.finrank_prod, Module.finrank_prod,times2 _ q,times2 _ u]

lemma sym_count : finrank ℂ SymT=7 := by
  have a:= invoice symAct four (by change Module.Finite ℂ (TT recG gFour); rw [t_classG]; exact finite_line _)
    (by change Module.Finite ℂ (TT ph fFour); rw [t_classF]; exact finite_line _) (by
    change Module.Finite ℂ (TT recX xFour); rw [t_classX]; infer_instance)
  change finrank ℂ SymT=finrank ℂ (TT recG gFour)+(2*finrank ℂ (TT ph fFour)+2*finrank ℂ (TT recX xFour)) at a
  simpa [g_ranks, f_ranks.1, x_ranks] using a
lemma vector_count : finrank ℂ OneW=6 := by
  have a:=invoice Raw.v five (by change Module.Finite ℂ (WW recG gFive); rw [w_classG]; exact finite_line _)
    (by change Module.Finite ℂ (WW ph fFive); rw [w_classF]; exact finite_line _)
    (by change Module.Finite ℂ (WW recX xFive); rw [w_classX]; exact finite_line _)
  change finrank ℂ OneW=finrank ℂ (WW recG gFive)+(2*finrank ℂ (WW ph fFive)+2*finrank ℂ (WW recX xFive)) at a
  simpa [g_ranks, f_ranks, x_ranks] using a
lemma pair_count : finrank ℂ BothV=60 := by
  have a:=invoice vsAct five (by change Module.Finite ℂ (VV recG gFive); rw [v_classG]; exact finite_line _)
    (by change Module.Finite ℂ (VV ph fFive); rw [v_classF]; exact finite_line _)
    (by change Module.Finite ℂ (VV recX xFive); rw [v_classX]; exact finite_line _)
  change finrank ℂ BothV=finrank ℂ (VV recG gFive)+(2*finrank ℂ (VV ph fFive)+2*finrank ℂ (VV recX xFive)) at a
  simpa [g_ranks, f_ranks, x_ranks] using a
-- Establish instances usable on frame & projected subtypes
instance finiteInvariant (d : Floor) {I} (A : Labels I) [Fintype I] : Module.Finite ℂ (invariant A d) := by
  -- tweak
  exact @FiniteDimensional.finiteDimensional_submodule ℂ (I → UV d) _ _ _ _ (invariant A d)

lemma r93 : finrank ℂ (LinearMap.range combMap)=59 := by
  letI : AddCommGroup ↥OneW := @Submodule.addCommGroup ℂ (Axis → UV five) _ _ _ OneW
  letI : AddCommGroup ↥BothV := @Submodule.addCommGroup ℂ (VS → UV five) _ _ _ BothV
  haveI := Free.of_divisionRing ℂ ↥OneW
  haveI := Free.of_divisionRing ℂ ↥BothV
  have h := @LinearMap.finrank_range_add_finrank_ker ℂ (OneW×BothV) _ _ _ (Axis × Axis → Shell) _ _ _ combMap
  rw [exact_93,LinearMap.finrank_range_of_inj combo_unique, Module.finrank_prod,vector_count, pair_count,sym_count] at h
  omega
end Calibration
end YM.GaugeFieldConstruction
