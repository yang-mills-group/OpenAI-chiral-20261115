import YM.CF.BProof.Extension.Packing

/-! Sphere extension with uniform Lipschitz bound. Supplies the Lipschitz entity
fillers for lem:B-moX, lem:B-frames (there in several successive columns), including
in the use on discrete grid boundaries. We prove the uniform extension using elementary
sphere avoidance (codimension > dimension of cell). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Extension
open Function MeasureTheory Measure Filter Metric Submodule Set Module
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

section
variable {A D : Type*} [PseudoMetricSpace A] [SeminormedAddCommGroup D]
/-- Lip price in ℝ. -/
def Lip (S : Set A) (K : ℝ) (f : A → D) := ∀ x ∈ S,∀ y ∈ S, ‖f x - f y‖ ≤ K*dist x y
lemma lip_iff (S : Set A) (K : ℝ≥0) (f : A → D) : Lip S K f ↔ LipschitzOnWith K f S := by
  unfold Lip; simp_rw [← dist_eq_norm]; simp [lipschitzOnWith_iff_dist_le_mul]
variable {S T : Set A} {K L : ℝ} {f g : A→D}
lemma Lip.add (h : Lip S K f) (v : Lip S L g) : Lip S (K+L) (fun x=> f x+g x) := fun x hx y hy => by
 rw [add_mul,add_sub_add_comm]; exact (norm_add_le ..).trans (add_le_add (h x hx y hy) (v x hx y hy))
lemma Lip.mono (h : Lip S K f) (u : T ⊆ S) (v : K≤L) : Lip T L f := fun x hx y hy=> (h _ (u hx) _ (u hy)).trans (by gcongr)
lemma Lip.norm (h : Lip S K f) : Lip S K (fun x=> ‖f x‖) := fun x hx y hy=> by rw [Real.norm_eq_abs]; exact (abs_norm_sub_norm_le ..).trans (h _ hx _ hy)
lemma normalizeLip [NormedSpace ℝ D] {δ : ℝ} (h : Lip S K f) (hq : 0<δ) (v : ∀ x∈S,δ ≤ ‖f x‖) : Lip S (2/δ*K) (fun x=> ‖f x‖⁻¹ • f x) := by
 intro x hx y hy; let a:= f x; let b:= f y; let r:= ‖a‖; let s:=‖b‖; have hp : 0<r:= hq.trans_le (v x hx); have ht: 0<s:= hq.trans_le (v y hy)
 have hh : ‖(r⁻¹-s⁻¹) • b‖ ≤ r⁻¹*‖a-b‖:= calc
   _ = r⁻¹*|r-s| := by rw [norm_smul, Real.norm_eq_abs, inv_sub_inv' hp.ne' ht.ne', abs_mul,abs_mul,abs_inv,abs_inv,abs_of_pos hp,abs_of_pos ht,abs_sub_comm]; change r⁻¹*_ * s⁻¹*s=r⁻¹*|r-s|; field_simp
   _ ≤ _ := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le ..) (by positivity)
 change ‖r⁻¹ • a-s⁻¹ • b‖ ≤ _
 rw [show r⁻¹ • a-s⁻¹ • b=r⁻¹ • (a-b)+(r⁻¹-s⁻¹) • b from by rw [smul_sub,sub_smul]; abel]
 apply (norm_add_le ..).trans; rw [norm_smul,Real.norm_of_nonneg (by positivity)]
 apply le_trans (add_le_add_right hh _ : _ ≤ r⁻¹*‖a-b‖+r⁻¹*‖a-b‖)
 rw [div_eq_mul_inv,mul_assoc,mul_assoc,← two_mul]; gcongr
 · exact v x hx
 exact h x hx y hy
end

/-- Simultaneously avoid arbitrary moving targets, including between net points. -/
theorem avoids (B K C s : ℝ) (hb : 0<B) (hk : 0<K) (hc : 0<C) (hs : 0<s) (hp : s ≤ 1) :
    ∃ r, 0<r ∧ ∀ (S : Set X) (P : X→Submodule ℝ Y) (f : X→Y), S ⊆ closedBall 0 B →
    Lip S K (fun x=> (P x).starProjection) → Lip S C f →
    (∀ x∈S, finrank ℝ X < finrank ℝ (P x)) →
    ∃ v : Y, ‖v‖ ≤ s ∧ ∀ x∈S,r≤ ‖(P x).starProjection v-f x‖ := by
 classical
 let a:= finrank ℝ X; let d:= finrank ℝ Y; let D:=1+K+C; have hD:0<D:=by unfold D; positivity
 letI : MeasurableSpace Y:= borel Y; letI : BorelSpace Y:=⟨rfl⟩; let μ : Measure Y:= Measure.addHaar; letI := FiniteDimensional.proper ℝ Y
 haveI : IsAddHaarMeasure μ:=by unfold μ; infer_instance; 
 let b:= μ.real (ball 0 1); have hy:0<b:= ENNReal.toReal_pos (IsOpen.measure_pos μ isOpen_ball (nonempty_ball.mpr zero_lt_one)).ne' measure_ball_lt_top.ne
 let L:=(4*B)^a*(8^d*D^(a+1)*b); have hl:0<L:=by dsimp only [L]; positivity
 let r:= min (min B (1/D)) (s^d*b/(2*L)); have hr:0<r:=lt_min (lt_min hb (by positivity)) (by positivity)
 let t:=D*r; have ht:0<t:=by dsimp only [t]; positivity; 
 have hT:t≤1:=by unfold t; rw [mul_comm]; exact (le_div_iff₀ hD).mp ((min_le_left ..).trans (min_le_right ..))
 refine ⟨r,hr,fun S P f hV hx hu hP=>?_⟩
 obtain ⟨i,hi,hN,hq⟩:=mesh S hr hb hV ((min_le_left ..).trans (min_le_left ..))
 let Q(x:X):= {y:Y| ‖y‖≤1 ∧ ‖(P x).starProjection y-f x‖≤t}
 have hz(x:X) : μ (Q x)<⊤ := lt_of_le_of_lt (measure_mono (show Q x ⊆closedBall (0:Y) 1 from fun _ hu=> mem_closedBall.mpr (by rw [dist_zero_right]; exact hu.1))) measure_closedBall_lt_top
 have he : μ.real (⋃ x∈i,Q x) ≤ L*r := calc
   _ ≤ ∑ x∈i, μ.real (Q x):= measureReal_biUnion_finset_le i Q
   _ ≤ ∑ x∈i, (8^d*t^(a+1)*b):= Finset.sum_le_sum fun x h=> (affineTube μ (P x) (f x) ht hT).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht.le hT (hP _ (hi h))) (by positivity)) hy.le)
   _ ≤ (4*B/r)^a * (8^d*t^(a+1)*b) := by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hN (by positivity)
   _ = _ := by unfold t L; rw [div_pow,mul_pow D r,pow_succ r]; field_simp
 have hv : ¬ closedBall (0:Y) s ⊆ ⋃ x∈i,Q x:=by
   intro g; have hh : s^d*b ≤ L*r := le_trans (by rw [← Measure.addHaar_real_closedBall μ 0 hs.le]; exact measureReal_mono g (measure_biUnion_lt_top i.finite_toSet (fun x _ => hz x)).ne) he -- tune
   have hu:= (le_div_iff₀ (by positivity : 0<2*L)).mp (min_le_right (min B (1/D)) (s^d*b/(2*L))); change _ ≤ _ at hu
   dsimp only [r] at hh; nlinarith [pow_pos hs d]
 obtain ⟨v,hv,H⟩:= Set.not_subset.mp hv; have hp' : ‖v‖≤s:= by simpa only [mem_closedBall,dist_zero_right] using hv
 refine ⟨v,hp',fun x ht'=>?_⟩
 obtain ⟨y,Y',Y''⟩:= hq x ht'
 have H':t < ‖(P y).starProjection v-f y‖:=lt_of_not_ge fun ha=> H (mem_iUnion₂.mpr ⟨_,Y',hp'.trans hp,ha⟩)
 have he := hi Y'; apply le_of_not_gt; intro hi'; apply H'.not_ge
 have hl : ‖(P x).starProjection v-(P y).starProjection v‖≤ K*dist x y:= calc
    _ ≤ ‖(P x).starProjection-(P y).starProjection‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _ -- tune
    _ ≤ K*dist x y := (mul_le_of_le_one_right (norm_nonneg _) (hp'.trans hp)).trans (hx _ ht' _ he)
 calc
   _ ≤ ‖(P y).starProjection v-(P x).starProjection v‖ + ‖(P x).starProjection v-f y‖ := norm_sub_le_norm_sub_add_norm_sub ..
   _ ≤ K*r + (r+C*r):= add_le_add (by rw [norm_sub_rev]; exact hl.trans (by gcongr)) ((norm_sub_le_norm_sub_add_norm_sub _ (f x) _).trans (add_le_add hi'.le ((hu x ht' y he).trans (by gcongr))))
   _ = _:=by unfold t D; ring
end YM.CF.BProof.Extension
