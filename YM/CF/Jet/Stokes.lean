/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Push.STATIONARY_UNIFORM.Calculus
/-! Adapt calculus to *finite smoothness*. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Filter Function Set Metric
open scoped Topology ContDiff BigOperators

section Jets

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Norms through n, *including the value*. Use on each read of a score (later
sum & derive localization of its tensors, don't claim a sup→scalar bound
uniform in volume on the summed score). -/
structure Allows (n : ℕ) (f : E → F) (x : E) (C : ℝ) : Prop where
  smooth : ContDiffAt ℝ n f x
  norm_le (k : ℕ) : k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ C

variable {n k : ℕ} {x : E} {f f' : E → F} {g : F → G} {C K M : ℝ}

lemma Allows.nonneg (h : Allows n f x C) : 0 ≤ C := (norm_nonneg _).trans (h.norm_le 0 (Nat.zero_le _))
lemma Allows.value (h : Allows n f x C) : ‖f x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using h.norm_le 0 (Nat.zero_le _)

lemma Allows.mono (h : Allows n f x C) (hC : C ≤ M) : Allows n f x M :=
  ⟨h.smooth, fun _ hk => (h.norm_le _ hk).trans hC⟩
lemma Allows.order (h : Allows n f x C) (hk : k ≤ n) : Allows k f x C :=
  ⟨h.smooth.of_le (by exact_mod_cast hk), fun _ hj => h.norm_le _ (hj.trans hk)⟩
lemma Allows.germ (h : Allows n f x C) (he : f =ᶠ[𝓝 x] f') : Allows n f' x C := by
  refine ⟨h.smooth.congr_of_eventuallyEq he.symm, fun k hk => ?_⟩
  rw [← (he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]; exact h.norm_le _ hk

lemma allows_const (x : E) {v : F} (hv : ‖v‖ ≤ C) : Allows n (fun _ : E => v) x C := by
  refine ⟨contDiffAt_const, fun k _ => ?_⟩
  by_cases hk : k=0
  · subst k; rwa [norm_iteratedFDeriv_zero]
  rw [iteratedFDeriv_const_of_ne hk, Pi.zero_apply,norm_zero]
  exact (norm_nonneg _).trans hv

lemma allows_linear {L : E →L[ℝ] F} (h : ‖L‖ ≤ C) (h' : ‖L x‖ ≤ C) : Allows n L x C := by
  refine ⟨L.contDiff.contDiffAt, fun k _ => ?_⟩
  cases k with
  | zero => rwa [norm_iteratedFDeriv_zero]
  | succ k =>
    rw [iteratedFDeriv_succ_eq_comp_right,comp_apply, LinearIsometryEquiv.norm_map]
    simp_rw [L.fderiv]
    cases k with
    | zero => rwa [norm_iteratedFDeriv_zero]
    | succ k => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply]; change ‖(0 : ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => E) (E →L[ℝ] F))‖ ≤ C; exact (@norm_zero (ContinuousMultilinearMap ℝ (fun _ : Fin (k+1) => E) (E →L[ℝ] F)) _).le.trans ((norm_nonneg L).trans h)

lemma Allows.add (h : Allows n f x C) (h' : Allows n f' x K) : Allows n (fun u => f u + f' u) x (C+K) := by
  refine ⟨h.smooth.add h'.smooth, fun k hk => ?_⟩
  change ‖iteratedFDeriv ℝ k (f + f') _‖ ≤ _
  rw [iteratedFDeriv_add_apply (h.smooth.of_le (by exact_mod_cast hk)) (h'.smooth.of_le (by exact_mod_cast hk))]
  exact (norm_add_le ..).trans (add_le_add (h.norm_le _ hk) (h'.norm_le _ hk))

lemma Allows.smul (h : Allows n f x C) (a : ℝ) : Allows n (fun u => a • f u) x (|a| * C) := by
  refine ⟨h.smooth.const_smul _, fun k hk => ?_⟩
  change ‖iteratedFDeriv ℝ k (a • f) _‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (h.smooth.of_le (by exact_mod_cast hk)),norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (h.norm_le _ hk) (abs_nonneg _)

lemma allows_sum {ι : Type*} {s : Finset ι} {f : ι → E → F} {C : ι → ℝ} (h : ∀ i∈s, Allows n (f i) x (C i)) :
    Allows n (fun u => ∑ i∈s, f i u) x (∑ i∈s, C i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using allows_const (n:=n) x (v:=(0:F)) (C:=0) (by simp)
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun _ hj => h _ (Finset.mem_insert_of_mem hj))

lemma Allows.pair {g : E → G} (h : Allows n f x C) (h' : Allows n g x C) : Allows n (fun u => (f u, g u)) x C := by
  refine ⟨h.smooth.prodMk h'.smooth, fun k hk => ?_⟩
  rw [iteratedFDeriv_prodMk h.smooth h'.smooth (by exact_mod_cast hk),ContinuousMultilinearMap.opNorm_prod]
  exact max_le (h.norm_le _ hk) (h'.norm_le _ hk)

lemma allows_pi {ι : Type*} [Fintype ι] {f : E → (ι → F)} (hC : 0 ≤ C) (h : ∀ i, Allows n (fun x => f x i) x C) :
    Allows n f x C := by
  have he : ContDiffAt ℝ n f x := contDiffAt_pi.mpr fun i => (h i).smooth
  refine ⟨he, fun k hk => ContinuousMultilinearMap.opNorm_le_bound hC (fun v => ?_)⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (by positivity))).mpr; intro i
  let L : (ι → F) →L[ℝ] F := ContinuousLinearMap.proj i
  have hh : iteratedFDeriv ℝ k f x v i = iteratedFDeriv ℝ k (fun u => f u i) x v := by
    change L _ = iteratedFDeriv ℝ k (L ∘ f) x v
    rw [L.iteratedFDeriv_comp_left he (by exact_mod_cast hk)]; rfl
  rw [hh]
  exact ((iteratedFDeriv ℝ k (fun u => f u i) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((h i).norm_le _ hk) (by positivity))

lemma Allows.linear (L : F →L[ℝ] G) (h : Allows n f x C) (hL : ‖L‖ ≤ K) : Allows n (fun u => L (f u)) x (K*C) := by
  refine ⟨L.contDiff.contDiffAt.comp x h.smooth, fun k hk => ?_⟩
  exact (L.norm_iteratedFDeriv_comp_left h.smooth (n:=k) (by exact_mod_cast hk)).trans
    (mul_le_mul hL (h.norm_le _ hk) (norm_nonneg _) ((norm_nonneg _).trans hL))

lemma open_patch {n:ℕ} {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : E} {f : E → F}
    (h : ContDiffAt 𝕜 n f x) : ∃ s : Set E, x ∈ s ∧ IsOpen s ∧ ContDiffOn 𝕜 n f s := by
  obtain ⟨u,hu,he⟩ := h.contDiffOn (m:=(n:WithTop ℕ∞)) le_rfl (by simp)
  obtain ⟨s,hs,ht,hh⟩ := _root_.mem_nhds_iff.mp hu
  exact ⟨s,hh,ht,he.mono hs⟩

def composeCost (n : ℕ) (K C : ℝ) : ℝ := (n.factorial:ℝ) * K * (1+C)^n
lemma Allows.comp (hg : Allows n g (f x) K) (hf : Allows n f x C) : Allows n (fun u => g (f u)) x (composeCost n K C) := by
  have hs : ContDiffAt ℝ n (g ∘ f) x := hg.smooth.comp x hf.smooth
  refine ⟨hs, fun k hk => ?_⟩
  obtain ⟨t,ht,ht',H⟩ := open_patch hg.smooth
  obtain ⟨u,hu,hu',H'⟩ := open_patch hf.smooth
  obtain ⟨s,he,he',hm⟩ := _root_.mem_nhds_iff.mp (inter_mem (hu'.mem_nhds hu)
    (hf.smooth.continuousAt.preimage_mem_nhds (ht'.mem_nhds ht)))
  have hx : 1 ≤ 1+C := le_add_of_nonneg_right hf.nonneg
  change ‖iteratedFDeriv ℝ k (g ∘ f) _‖ ≤ _
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv he'.uniqueDiffOn (hs.of_le (by exact_mod_cast hk)) hm]
  apply le_trans (norm_iteratedFDerivWithin_comp_le H (H'.mono fun i hi => (he hi).1) (by exact_mod_cast hk) ht'.uniqueDiffOn he'.uniqueDiffOn
    (fun y hy => (he hy).2) hm (C:=K) (D:=1+C) ?_ ?_) ?_
  · intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv ht'.uniqueDiffOn (hg.smooth.of_le (by exact_mod_cast hi.trans hk)) ht]
    exact hg.norm_le i (hi.trans hk)
  · intro i hi hj
    rw [iteratedFDerivWithin_eq_iteratedFDeriv he'.uniqueDiffOn (hf.smooth.of_le (by exact_mod_cast hj.trans hk)) hm]; apply (hf.norm_le _ (hj.trans hk)).trans
    exact le_trans (le_add_of_nonneg_left zero_le_one) (le_self_pow₀ hx (by omega))
  have hK := hg.nonneg
  unfold composeCost
  gcongr

lemma Allows.bilinear (L : F →L[ℝ] G →L[ℝ] D) {g : E → G} (hf : Allows n f x C) (hg : Allows n g x K) (h : ‖L‖ ≤ M) :
    Allows n (fun y => L (f y) (g y)) x (2^n * M * C * K) := by
  refine ⟨(L.contDiff.contDiffAt.comp x hf.smooth).clm_apply hg.smooth, fun k hk => ?_⟩
  have hm := (norm_nonneg L).trans h
  have hc := hf.nonneg
  have hh := hg.nonneg
  obtain ⟨u,hu,hu',H⟩ := open_patch hf.smooth
  obtain ⟨s,hs,hs',H'⟩ := open_patch hg.smooth
  have hsu : UniqueDiffOn ℝ (s ∩ u) := (hs'.inter hu').uniqueDiffOn
  have hx : x ∈ s∩u := ⟨hs,hu⟩
  have he : ContDiffAt ℝ n (fun y => L (f y) (g y)) x :=
    (L.contDiff.contDiffAt.comp x hf.smooth).clm_apply hg.smooth
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hsu (he.of_le (by exact_mod_cast hk)) hx]
  apply le_trans (L.norm_iteratedFDerivWithin_le_of_bilinear (H.mono inter_subset_right) (H'.mono inter_subset_left) hsu hx (by exact_mod_cast hk)) ?_
  -- Leibniz bound
  calc
    _ ≤ M * ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ) * C * K := by
      refine mul_le_mul h (Finset.sum_le_sum fun i hi => ?_) ?_ hm
      · have hi := Finset.mem_range.mp hi
        rw [iteratedFDerivWithin_eq_iteratedFDeriv hsu (hf.smooth.of_le (by exact_mod_cast (show i ≤ n by omega))) hx,
          iteratedFDerivWithin_eq_iteratedFDeriv hsu (hg.smooth.of_le (by exact_mod_cast (show k-i≤ n by omega))) hx]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hf.norm_le i (by omega)) (by positivity))
          (hg.norm_le _ (by omega)) (norm_nonneg _) (by positivity)
      positivity
    _ = 2^k * M * C * K := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]; ring
    _ ≤ _ := by gcongr; norm_num

end Jets
end YM.CF.Jet
