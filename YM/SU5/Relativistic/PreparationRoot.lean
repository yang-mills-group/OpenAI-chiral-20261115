import YM.SU5.Selected.Panes

/-! # Every Issued sample has approximants by actual ground vectors.

No conflation of a.e.-sampled components with another. Only engineering freedom
is the bump: nothing changed in the phase selection. Generic analysis part.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Ground.Panes
open Function Set Filter MeasureTheory Measure Spectral TopologicalSpace WeakDual
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators
section issuance
variable {A : Type} [CommCStarAlgebra A] {H : Hilbert} (p : A →⋆ₐ[ℂ] H.Op) (w : H)
variable {R : Panes A} (h : R.Shines H p w) (x : R.X)
local notation "Θ" => R.character
local notation "X" => R.X
local notation "μ" => R.μ
include h
lemma Shines.realizes (f : C(R.X, ℂ)) : ∃ a : A, ∀ i, R.character i a = f i := by
  choose y b using fun i : X => bij.surjective (Θ i)
  have hp : Continuous y := by
    have hy : Continuous (fun i : X => (y i).val) := by
      apply WeakDual.continuous_of_continuous_eval
      intro a
      change Continuous (fun i => view (y i) a); simp_rw [b]; exact h.weak _
    exact Continuous.subtype_mk hy fun i => (y i).property
  have hy : Bijective y := by
    refine ⟨fun i j p => ?_, fun z => ?_⟩
    · apply h.onto.injective; rw [← b,← b,p]
    obtain ⟨i,p⟩:= h.onto.surjective (view z)
    exact ⟨i,bij.injective ((b i).trans p)⟩
  let e:X ≃ₜ Theta («X»:=A):= (Equiv.ofBijective y hy).toHomeomorphOfContinuousClosed hp hp.isClosedMap
  let g : C(Theta («X»:=A), ℂ):= ⟨fun x=> f (e.symm x), f.continuous.comp e.symm.continuous⟩
  obtain ⟨a,q⟩:= (gelfandStarTransform A).surjective g
  refine ⟨a,fun i=>?_⟩; rw [← b]; change gelfandStarTransform A a (y i) = _
  change gelfandStarTransform A a=g at q
  rw [q]; exact congrArg f (e.symm_apply_apply i)

/-- A unit approximant with spectral weight in the ball. -/
lemma Shines.locates {r : ℝ}(hr:0 < r): ∃ a : A, ‖p a w‖=1 ∧
    (∀ x':R.X, r ≤ dist x' x → R.character x' a = 0) := by
  letI := h.normalized; letI := h.support
  let f : C(X,ℂ) := ⟨fun i=> ((max 0 (r-dist i x):ℝ):ℂ),by fun_prop⟩
  obtain ⟨a,b⟩:= h.realizes p w f
  let J := fun i : X => ‖f i‖^2
  have ht : Continuous J:= f.continuous.norm.pow _
  have hf : 0 < J x := by
     have h' : f x = (r:ℂ):= by simp [f,hr.le]
     dsimp only [J]; rw [h',Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]; positivity
  have he : ‖p a w‖^2 = ∫ i, J i ∂ μ := by
      rw [← h.energyMatch]; simp_rw [b]; rfl
  have hv : ‖p a w‖ ≠ 0 := by
      have hl : 0 < ‖p a w‖^2 := he.symm ▸ (ht.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _) (fun i => sq_nonneg _) (ne_of_gt hf))
      intro t; rw [t] at hl; norm_num at hl
  let c:ℂ := ((‖p a w‖⁻¹:ℝ):ℂ)
  have hc:‖c‖=‖p a w‖⁻¹:= by simp [c]; -- check
  refine ⟨c • a,?_,?_⟩
  · rw [map_smul]; change ‖c • p a w‖=1; rw [norm_smul,hc,inv_mul_cancel₀ hv]
  intro i k; rw [map_smul,b]
  simp [f, max_eq_left (sub_nonpos.mpr k)]

lemma Shines.spectral_distance {f : A} (t : ‖p f w‖ = 1) {r : ℝ} (hs : ∀ i : X, r ≤ dist i x → Θ i f = 0)
    (i : A) {ε : ℝ}(e : 0≤ε)(k : ∀ x':X, dist x' x < r→‖Θ x' i - Θ x i‖ ≤ ε) :
    ‖p i (p f w)-(Θ x i) • p f w‖ ≤ ε := by
  letI:= h.normalized
  have he : p i (p f w)-(Θ x i) • p f w = p (i*f-(Θ x i) • f) w := by rw [map_sub,map_mul,map_smul]; rfl
  let g:=i*f-(Θ x i) • f
  have hu : ‖p g w‖^2 ≤ ε^2 := calc
   ‖p g w‖^2 = ∫ x', ‖Θ x' g‖^2 ∂ μ := (h.energyMatch _).symm
   _ ≤ ∫ x', ε^2 * ‖Θ x' f‖^2 ∂ μ := by
    refine integral_mono (((h.weak g).norm.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((continuous_const.mul ((h.weak f).norm.pow _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun u=> ?_
    have ht: Θ u g=(Θ u i - Θ x i)*Θ u f:=by unfold g; rw [map_sub,map_mul,map_smul,sub_mul]; rfl
    rcases lt_or_ge (dist u x) r with v|v
    · rw [ht,norm_mul,mul_pow]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (k u v) _) (sq_nonneg _)
    simp [ht,hs u v]
   _ = ε^2 := by rw [integral_const_mul,h.energyMatch f,t]; simp
  rw [he]; change ‖p g w‖ ≤ ε; nlinarith only [e,hu]
omit h in
lemma form_distance {f : A} (t : ‖p f w‖=1) {ε:ℝ} (a:A)
    (h : ‖p a (p f w)-(Θ x a) • p f w‖ ≤ ε) : ‖inner ℂ (p f w) (p a (p f w)) - Θ x a‖ ≤ ε := by
  have he : inner ℂ (p f w) ((Θ x a) • p f w)=Θ x a:= by
     rw [inner_smul_right,inner_self_eq_norm_sq_to_K,t]; simp
  nth_rw 1 [← he]; rw [←inner_sub_right]
  exact (norm_inner_le_norm ..).trans (by rwa [t,one_mul])

/-- Applies to every character sample, even one off of a given conull set. -/
lemma Shines.chosen_at : ∃ f : ℕ → A, (∀ i:ℕ, ‖p (f i) w‖=1) ∧
    (∀ a:A,Tendsto (fun i=> p a (p (f i) w)-(R.character x a) • p (f i) w) atTop (𝓝 0)) ∧
    ∀ a:A,Tendsto (fun i=> inner ℂ (p (f i) w) (p a (p (f i) w))) atTop (𝓝 (R.character x a)) := by
  let r := fun i:ℕ=> (1/2:ℝ)^i
  have hr:Tendsto r atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  choose f u v using fun i:ℕ=> h.locates p w x (r:=r i) (by unfold r; positivity)
  have hf(a:A)(ε:ℝ)(hq:0<ε):∀ᶠ i in atTop, ‖p a (p (f i) w)-(Θ x a) • p (f i) w‖ < ε := by
    have hx := h.weak a
    obtain ⟨δ,hδ,t⟩:= Metric.continuousAt_iff.mp (hx.continuousAt (x:=x)) (ε/2) (by linarith)
    filter_upwards [hr.eventually (gt_mem_nhds hδ)] with i (g : r i<δ)
    exact lt_of_le_of_lt (h.spectral_distance p w x (u i) (v i) a (ε:=ε/2) (by linarith) (fun x' k => by simpa [dist_eq_norm] using (t (lt_trans k g)).le)) (by linarith)
  refine ⟨f,u,fun i=> Metric.tendsto_nhds.mpr fun ε k=> ?_,fun i=> Metric.tendsto_nhds.mpr fun ε k=>?_⟩
  · simpa only [dist_zero_right] using hf i ε k
  filter_upwards [hf i ε k] with n e
  rw [dist_eq_norm]; exact lt_of_le_of_lt (form_distance p w x (u n) i (le_refl _)) e
end issuance
end YM.OS.Ground.Panes
#print axioms YM.OS.Ground.Panes.Shines.chosen_at
