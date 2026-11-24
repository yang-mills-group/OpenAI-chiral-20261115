import YM.CF.Newt.Yolk
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior Finset MeasureTheory
  Metric AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {X E F H:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 [NormedAddCommGroup H][NormedSpace ℝ H]{a C K M r d s B D:ℝ}{x:E}{f g:E→F}{n:ℕ}
lemma portrait (h: n≥2)(p:Portrait f (0:E→L[ℝ] F) n s r C)(ht:0≤s)(hS:s≤r)(hw:s≤1)(hv: ‖x‖ ≤ 1): Jet.Allows n (fun x=> f (s • x)) x (2*C*s^2):=by
 let L:= s • ContinuousLinearMap.id ℝ E; have hL : ‖L‖≤s:=by unfold L; rw [norm_smul, Real.norm_of_nonneg ht]; exact mul_le_of_le_one_right ht ContinuousLinearMap.norm_id_le
 have hp : ‖L x‖ ≤ s:= ((L.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) hv).trans hL))
 obtain ⟨he,hB⟩:=p.uniform (L x) (hp.trans hS); have hC:= (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
 refine ⟨he.comp x L.contDiff.contDiffAt,fun j hj=>?_⟩
 change ‖iteratedFDeriv ℝ j (f ∘ L) _‖≤ _
 by_cases hq:j=0; · subst j; have hh:= p.zeroth_charge h hp hS; simpa only [norm_iteratedFDeriv_zero, Function.comp_apply, ContinuousLinearMap.zero_apply, sub_zero, show C*(s+s)*s=2*C*s^2 by ring] using hh
 rw [Push.Uniform.iter_lin_at (he.of_le (by exact_mod_cast hj))]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
 rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin]; by_cases hy : j=1
 · subst j; rw [norm_iteratedFDeriv_one,pow_one]; have he:= p.first_charge h (hp.trans hS); rw [sub_zero] at he
   apply (mul_le_mul he hL (norm_nonneg L) ((norm_nonneg _).trans he)).trans
   apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hp) hC) ht).trans_eq (by ring)
 apply (mul_le_mul (hB j hj) ((pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_of_le_one ht hw (by omega : 2≤j))) (pow_nonneg (norm_nonneg _) _) hC).trans
 rw [mul_assoc]; nlinarith [mul_nonneg hC (sq_nonneg s)]
lemma subtract_p (h:Jet.Allows n f x C)(p:Jet.Allows n g x K): Jet.Allows n (fun x=> f x-g x) x (C+K):= by
 have hP:= h.add (p.smul (-1)); simpa only [neg_one_smul,abs_neg,abs_one, one_mul,←sub_eq_add_neg] using hP
lemma cling (Q E:Type) [NormedAddCommGroup Q][NormedSpace ℝ Q][NormedAddCommGroup E][NormedSpace ℝ E]: ‖(ContinuousLinearMap.apply ℝ E (E:=Q)).flip‖≤1:=by -- tune
 refine ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun i j=>?_ ; rw [one_mul]; exact i.le_opNorm j
lemma appliance {P:E→ F →L[ℝ] H}(h:Jet.Allows n P x C)(p:Jet.Allows n f x K):Jet.Allows n (fun y=>P y (f y)) x (2^n*C*K):=by
 have he:= h.bilinear (ContinuousLinearMap.apply ℝ H|>.flip) p (cling F H); rwa [mul_one] at he
lemma joint {P:E→ F →L[ℝ] E}{Q:E→H →L[ℝ] F}(h:Jet.Allows n P x C)(p:Jet.Allows n Q x K) : Jet.Allows n (fun y=> (P y).comp (Q y)) x (2^n*C*K):=by
 have ht:= h.bilinear (ContinuousLinearMap.compL ℝ H F E) p (ContinuousLinearMap.norm_compL_le ..); rwa [mul_one] at ht
lemma pole0 (s:ℝ) (B H:Type) [NormedAddCommGroup B][NormedSpace ℝ B] [NormedAddCommGroup H][NormedSpace ℝ H]
 (p:0≤s) : ‖s • ContinuousLinearMap.id ℝ B‖ ≤ s:= by rw [norm_smul, Real.norm_of_nonneg p]; exact mul_le_of_le_one_right p ContinuousLinearMap.norm_id_le
lemma miles (hn:1≤n)(hw:∀ v: E, ‖v‖<r→Jet.Allows n f v C)(h:0<r)(hx:‖x‖<r): ‖f x-f 0‖≤ C*‖x‖:=by
 have ht y (hy:y∈ball (0:E) r):= (hw y (mem_ball_zero_iff.mp hy)).order hn
 have hh:= (convex_ball (0:E) r).norm_image_sub_le_of_norm_fderiv_le (C:=C) (f:=f) (fun i hi => (ht _ hi).smooth.differentiableAt (by norm_num)) (fun i hi=> ?_) (mem_ball_self h) (mem_ball_zero_iff.mpr hx)
 · simpa using hh
 simpa only [norm_iteratedFDeriv_one] using (ht _ hi).norm_le 1 le_rfl
lemma near_s (p:0 ≤ s)(hp:s≤1)(hn:1≤n)(hr:s<r)(hw:∀ v:E, ‖v‖<r→Jet.Allows n f v C)(hy:‖x‖≤1):
 Jet.Allows n (fun y=> f (s • y)- f 0) x (C*s):=by
 let L:=s • ContinuousLinearMap.id ℝ E; have hL:‖L‖≤s:=pole0 s E E p; have hv : ‖L x‖≤s:= ((L.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) hy).trans hL))
 have ht:= hw (L x) (hv.trans_lt hr)
 have hm : ContDiffAt ℝ n (f ∘ L) x := ht.smooth.comp _ L.contDiff.contDiffAt
 refine ⟨hm.sub contDiffAt_const,fun i hi=> ?_⟩
 change ‖iteratedFDeriv ℝ i ((f∘ L)-fun _=> f 0) _‖ ≤ _; cases i with
 | zero => rw [norm_iteratedFDeriv_zero]; exact (miles hn hw (p.trans_lt hr) (hv.trans_lt hr)).trans (mul_le_mul_of_nonneg_left hv ht.nonneg)
 | succ i => rw [iteratedFDeriv_sub_apply (hm.of_le (Nat.cast_le.mpr hi)) contDiffAt_const, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero, Push.Uniform.iter_lin_at (ht.smooth.of_le (Nat.cast_le.mpr hi))]
             refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (mul_le_mul (ht.norm_le _ hi) ?_ (prod_nonneg fun i _=> norm_nonneg _) ht.nonneg)
             rw [prod_const,Finset.card_univ,Fintype.card_fin]
             exact (pow_le_pow_left₀ (norm_nonneg _) hL _).trans ((pow_le_pow_of_le_one p hp (show 1 ≤ i+1 by omega)).trans_eq (pow_one _))
end YM.CF.Newt
