import Mathlib
/-! # Finite dimensional bounded semigroup averaging with uniform invertors. Variant to avoid additional continuity grants on Orbit consumers. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SU5.SatinWard.FieldBudgets
open Function Filter Set Metric
open scoped FiniteDimensional Topology NNReal BigOperators InnerProductSpace
variable {X ι:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
theorem averaging [Nonempty ι] (F:ι→ X→L[ℝ] X)(a:X)(C:ℝ)(u:0<C) (p:∀ i:ι,‖F i‖ ≤ C)(j:∀ i:ι,∃ k:ι,(F k).comp (F i)=ContinuousLinearMap.id ℝ X)(h:∀ i k:ι,∃ r:ι,(F i).comp (F k)=F r):∃ x∈closure (convexHull ℝ (range (fun i=>F i a))),∀ i:ι,F i x=x:=by
 let D:= EuclideanSpace ℝ (Fin (Module.finrank ℝ X)); let e:X≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X)):= (LinearEquiv.ofFinrankEq X (EuclideanSpace ℝ (Fin (Module.finrank ℝ X))) (finrank_euclideanSpace_fin (𝕜:=ℝ)).symm).toContinuousLinearEquiv
 let A(i:ι):=e.toContinuousLinearMap.comp (F i)
 let f(x:X):ℝ:=⨆i:ι, ‖A i x‖^(2:ℕ)
 let s:= range (fun i=>F i a); let t:= convexHull ℝ s; let S:= closure t
 have he(i k x) :∃ r,A i (F k x)= A r x:=by obtain ⟨r,u⟩:=h i k; exact ⟨r,congrArg e (DFunLike.congr_fun u x)⟩
 have hC(i:ι)(x:X): ‖F i x‖ ≤ C * ‖x‖:=(ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right (p i) (norm_nonneg x))
 let C':= C * (1+‖e.symm.toContinuousLinearMap‖); have hv:0≤ ‖e.symm.toContinuousLinearMap‖:= norm_nonneg _; have hu:0<C':=by unfold C'; positivity
 have hh(i:ι)(x:X): ‖x‖ / C' ≤ ‖A i x‖:=by
    obtain ⟨k,h⟩:=j i; have he: F k (F i x)=x:= DFunLike.congr_fun h x
    apply (div_le_iff₀ hu).2; rw [mul_comm]; apply Eq.trans_le (b:=‖F k (F i x)‖) (by rw [he]); apply (hC ..).trans
    have hp: ‖F i x‖ ≤ (1+‖e.symm.toContinuousLinearMap‖) * ‖A i x‖ :=by nth_rw 1 [← e.symm_apply_apply (F i x)]; exact (ContinuousLinearMap.le_opNorm e.symm.toContinuousLinearMap (A i x)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left hp u.le).trans_eq (by unfold C'; ring)
 have hb(x:X): BddAbove (range fun i:ι=>‖A i x‖^2):= by refine ⟨(‖e.toContinuousLinearMap‖*(C*‖x‖))^2,?_⟩; rintro t ⟨i,rfl⟩; apply pow_le_pow_left₀ (norm_nonneg _) _; exact (e.toContinuousLinearMap.le_opNorm (F i x)).trans (mul_le_mul_of_nonneg_left (hC i x) (norm_nonneg _)) -- tune
 have hf(i:ι)(x):‖A i x‖^2 ≤ f x:=le_ciSup (hb x) i
 have hS:S.Nonempty:= ( (range_nonempty (fun i=>F i a)).mono (subset_convexHull ℝ s)).mono subset_closure
 have hpS: Convex ℝ S:= (convex_convexHull ℝ s).closure
 have hx(i:ι): MapsTo (F i) S S:=by
    refine MapsTo.closure (?_: MapsTo (F i) t t) (F i).continuous; change t⊆ (F i)⁻¹' t
    apply convexHull_min _ ((convex_convexHull ℝ s).linear_preimage (F i).toLinearMap) -- tune arg
    rintro t ⟨j,rfl⟩; obtain ⟨r,w⟩:=h i j; exact subset_convexHull ℝ s (mem_range.mpr ⟨r,Eq.symm (DFunLike.congr_fun w a)⟩)
 have hK:IsCompact S:=by
    let U:= closedBall (0:X) (C*‖a‖); exact (isCompact_closedBall ..).of_isClosed_subset isClosed_closure (closure_minimal (show t⊆U from convexHull_min (range_subset_iff.mpr fun i=>mem_closedBall_zero_iff.mpr (hC i a)) (convex_closedBall (0:X) (C*‖a‖))) isClosed_closedBall)
 obtain ⟨x,y,p⟩:= LowerSemicontinuousOn.exists_isMinOn hS hK ( (show LowerSemicontinuous f from lowerSemicontinuous_ciSup hb (fun i=> ( (A i).continuous.norm.pow 2).lowerSemicontinuous)).lowerSemicontinuousOn S)
 refine ⟨x,y,fun i=>?_⟩; let z:= F i x; by_contra v; have hv:0 < ‖z-x‖/C':=div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr v)) hu
 have hhu: f z ≤ f x:=by refine ciSup_le (fun j=> ?_); obtain ⟨r,h⟩:= he j i x; change ‖A j z‖^2≤_; rw [show A j z=A r x from h]; exact hf r x
 let w:=(1/2:ℝ) • z+(1/2:ℝ) • x
 have ht:f w ≤ f x-(1/4:ℝ)*(‖z-x‖/C')^2:=by
    apply ciSup_le; intro j; have hp:= hh j (z-x); rw [map_sub] at hp; change ‖A j w‖^2≤_; have he:= parallelogram_law_with_norm ℝ (A j z) (A j x); rw [show w=(1/2:ℝ) • (z+x) from (smul_add ..).symm,map_smul,map_add,norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ)≤1/2)]
    nlinarith only [hf j x,(hf j z).trans hhu,he, pow_le_pow_left₀ hv.le hp 2]
 linarith only [(show f x ≤ f w from p (hpS (hx i y) y (by norm_num) (by norm_num) (by norm_num))), ht, pow_pos hv 2]
end YM.SU5.SatinWard.FieldBudgets
