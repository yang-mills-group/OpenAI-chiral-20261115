import YM.CF.BProof.Extension.Avoid

/-! Uniform Lipschitz extension with sphere target (or into a bundle of such spheres,
real ambient fiber dimension ≥ base dimension + 1). This makes the uniform extension in
the manuscript elementary; in particular no homotopy classifier for lattice links is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension
open Function MeasureTheory Measure Filter Metric Set Submodule Module
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

private def taper (x : ℝ) : ℝ := max 0 (min 1 (2*(1-x)))
private lemma taper_pay (x y : ℝ) : 0 ≤ taper x ∧ taper x ≤1 ∧ |taper x-taper y|≤2*|x-y| := by
 unfold taper; grind -- tune max/min abs
private lemma projects {S : Set X} {K : ℝ} {P : X→Submodule ℝ Y} (hp : Lip S K (fun x=> (P x).starProjection)) (v : Y) (x y : X)
    (hx : x∈ S)(hy:y∈ S) : ‖(P x).starProjection v-(P y).starProjection v‖ ≤ K * ‖v‖ * dist x y :=
  calc
    _ ≤ ‖(P x).starProjection-(P y).starProjection‖ * ‖v‖ := ContinuousLinearMap.le_opNorm ..
    _ ≤ _:= (mul_le_mul_of_nonneg_right (hp x hx y hy) (norm_nonneg _)).trans_eq (mul_right_comm ..)

theorem sphere_extend (B K C : ℝ) (hb : 0<B) (hk : 0<K) (hc : 0<C) : ∃ L > (0:ℝ),
    ∀ (S T : Set X) (P : X→Submodule ℝ Y) (f : X→Y), S ⊆ closedBall 0 B → T ⊆ S → T.Nonempty →
    (∀ x∈S,finrank ℝ X < finrank ℝ (P x)) → Lip S K (fun x=> (P x).starProjection) →
    (∀ x ∈ T, ‖f x‖=1 ∧ f x∈P x) → Lip T C f →
    ∃ g : X→Y, EqOn f g T ∧ (∀ x∈S, ‖g x‖=1 ∧ g x ∈ P x) ∧ Lip S L g := by
 let c:ℝ≥0:=⟨C,hc.le⟩
 let a:ℝ := ↑(lipschitzExtensionConstant Y * c); have ha:0<a:=NNReal.coe_pos.mpr (mul_pos (lipschitzExtensionConstant_pos Y) (NNReal.coe_pos.mp (by exact hc)))
 let b:=1+a*(B+B); have hB:0<b:=by unfold b; positivity
 let u:=K*b+a; have hu:0<u:=by unfold u; positivity
 obtain ⟨r,hr,H⟩:= avoids (X:=X) (Y:=Y) B K u (1/4) hb hk hu (by norm_num) (by norm_num)
 let δ:= min r (1/4); have hδ:0<δ:=lt_min hr (by norm_num); let M:=u + (2*u+K); have hm:0<M:=by unfold M; positivity
 refine ⟨2/δ*M,by positivity,fun S T P f h ht hT hd hp hv hl=>?_⟩
 obtain ⟨p,hp'⟩:=hT
 obtain ⟨w,hw,he⟩:= ((lip_iff T c f).mp hl).extend_finite_dimension
 have hr' (x : X)(hx:x∈S) : ‖w x‖≤b := calc
   _ ≤ ‖w x-w p‖+‖w p‖:=norm_le_norm_sub_add ..
   _ ≤ a*dist x p + 1:=add_le_add (show ‖w x-w p‖≤_ by rw [← dist_eq_norm]; exact hw.dist_le_mul ..) ((he hp').symm.trans (Eq.refl _) ▸ (hv p hp').1.le) -- tune
   _ ≤ _ := by
      have hx' : dist x p ≤ B+B := (dist_triangle x 0 p).trans (add_le_add (h hx) (by rw [dist_comm]; exact (show dist p 0≤ B from h (ht hp')))); unfold b; rw [add_comm (1:ℝ)]; gcongr
 let Q(x:X):=(P x).starProjection; let g(x:X):=Q x (w x)
 have hQ:Lip S u g:=by
   intro x hx y hy
   refine le_trans (norm_sub_le_norm_sub_add_norm_sub _ (Q y (w x)) _) (le_trans (add_le_add (le_trans (projects hp (w x) _ _ hx hy) (show K*_ * _≤ K*b*dist x y from by gcongr; exact hr' x hx)) ?_) (by unfold u; rw [add_mul]))
   unfold g; rw [← map_sub]; exact ((P y).norm_starProjection_apply_le _).trans (by rw [← dist_eq_norm]; exact hw.dist_le_mul x y)
 obtain ⟨v,hw',hU⟩:= H S P (fun x=>-g x) h hp (fun x hx y hy => by rw [neg_sub_neg,norm_sub_rev]; exact hQ x hx y hy) hd
 have ho: ‖v‖ ≤ 1:= hw'.trans (by norm_num)
 let G(x:X):=g x+ taper ‖g x‖ • Q x v
 have hz (x : X)(hx : x∈ S) : δ ≤ ‖G x‖:=by
    obtain ⟨hp,hv,-⟩:= taper_pay ‖g x‖ 0
    by_cases H:2*‖g x‖ ≤1
    · have he:taper ‖g x‖=1:=by unfold taper; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      apply (min_le_left r _).trans; unfold G; rw [he,one_smul]; rw [add_comm]; exact (show _ from (by rw [← sub_neg_eq_add]; exact hU x hx))
    apply (min_le_right r (1/4)).trans; have hi : ‖taper ‖g x‖ • Q x v‖≤ 1/4:=by rw [norm_smul,Real.norm_of_nonneg hp]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hv) (((P x).norm_starProjection_apply_le _).trans hw')
    unfold G; have hh := norm_le_norm_sub_add (g x) (- (taper ‖g x‖ • Q x v)); rw [sub_neg_eq_add, norm_neg] at hh; linarith
 have heq : EqOn f G T := by
    intro x hx; obtain ⟨hm,hk⟩:=hv x hx; have hh : g x=f x:= by unfold g; rw [← he hx]; exact Submodule.starProjection_eq_self_iff.mpr hk
    simp [G,hh,hm,taper]
 let F(x:X):= ‖G x‖⁻¹ • G x
 refine ⟨F,fun x hx=>?_ ,fun x hx=>?_,normalizeLip ?_ hδ hz⟩
 · unfold F; simp [← heq hx, (hv x hx).1]
 · refine ⟨?_,(P x).smul_mem _ ((P x).add_mem (by simp [g, Q]) ((P x).smul_mem _ (by simp [Q])))⟩
   have ha : 0<‖G x‖:=hδ.trans_le (hz x hx); unfold F; rw [norm_smul, Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ ha.ne']
 apply hQ.add
 intro x hx y hy; let A:=taper ‖g x‖; let A':= taper ‖g y‖; let X':=Q x v; let Z:=Q y v
 have hf : ‖A-A'‖ ≤ 2*u*dist x y:=by rw [Real.norm_eq_abs,mul_assoc]; exact (taper_pay ‖g x‖ ‖g y‖).2.2.trans (mul_le_mul_of_nonneg_left (by simpa only [← Real.norm_eq_abs] using hQ.norm x hx y hy) (by positivity))
 change ‖A • X'-A' • Z‖ ≤ _
 rw [show A • X'-A' • Z=(A-A') • X'+A' • (X'-Z) from by rw [smul_sub,sub_smul]; abel,add_mul]
 apply (norm_add_le ..).trans; rw [norm_smul,norm_smul]; apply add_le_add
 · exact (mul_le_of_le_one_right (norm_nonneg _) (((P x).norm_starProjection_apply_le _).trans ho)).trans hf
 rw [Real.norm_of_nonneg (taper_pay ‖g y‖ 0).1]
 exact (mul_le_of_le_one_left (norm_nonneg _) (taper_pay _ 0).2.1).trans ((projects hp v _ _ hx hy).trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hk.le ho) dist_nonneg))
end YM.CF.BProof.Extension
