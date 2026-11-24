import Velour.Organza.Raising
/-!
# Accessible imaginary and real time spans of Gram prices
Using the actual energies on the domain of Velour/Organza. For any vector pair
with the second on that domain: a strict cross at a positive imaginary duration
is accessible also by real-time translations **arbitrarily small**, not just by
arbitrary translations. We need this to keep test charges normalized and
separated in their original boxes when changing to ensure a real discrepancy.
-/
set_option autoImplicit false
set_option maxRecDepth 2000

noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory Metric
open scoped NNReal Topology InnerProductSpace ComplexOrder

namespace Gingham
open Paley
namespace Air

variable {F : ℂ → ℂ} {a b D C : ℝ}

lemma convLoft : IsPreconnected loft := (convex_halfSpace_im_gt 0).isPreconnected

theorem squared_interval (h : Air F C) (lift :
    ∀ z : ℂ, 0 ≤ z.im → ‖F z - F z.re‖ ≤ D * z.im)
    (hab : a < b) (hD : 0 ≤ D)
    (h0 : ∀ t ∈ Ioo a b, F t = 0) :
    EqOn F 0 loft := by
  let G (z : ℂ) := if 0 < z.im then (F z)^2 else 0
  let s : Set ℂ := re ⁻¹' (Ioo a b)
  have ho : IsOpen s := isOpen_Ioo.preimage continuous_re
  have hdiff (z : ℂ) (p : z ∈ s) : DifferentiableAt ℂ G z := by
    rcases lt_trichotomy z.im 0 with hz|hz|hz
    · refine (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_im.tendsto z).eventually (gt_mem_nhds hz)]
        with w (hw : w.im < 0); exact if_neg (not_lt_of_gt hw)
    · have hG : G z = 0 := if_neg (by rw [hz]; exact lt_irrefl _)
      suffices HasDerivAt G 0 z from this.differentiableAt
      rw [hasDerivAt_iff_isLittleO_nhds_zero, hG]
      refine Asymptotics.IsBigO.trans_isLittleO (g := fun w : ℂ => w^2) ?_
        (by simpa using (Asymptotics.isLittleO_pow_pow (𝕜:=ℂ) (show 1 < 2 by decide)))

      simp only [sub_zero, smul_zero]
      apply Asymptotics.IsBigO.of_bound (D^2)
      have hs : ∀ᶠ w in 𝓝 (0:ℂ), z+w ∈ s :=
        ((tendsto_const_nhds (x:=z)).add tendsto_id).eventually
          (ho.mem_nhds (by simpa using p))
      filter_upwards [hs] with w e
      by_cases t : 0 < (z+w).im
      · rw [show G (z+w) = (F (z+w))^2 from if_pos t, norm_pow, norm_pow, ←mul_pow]
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [←sub_zero (F _), ← h0 _ e]
        refine (lift _ t.le).trans (mul_le_mul_of_nonneg_left ?_ hD)
        rw [add_im,hz,zero_add]; exact im_le_norm w
      rw [show G (z+w)=0 from if_neg t, norm_zero]; positivity
    have hp : z ∈ loft := hz
    refine ((h.straight z hp).differentiableAt (open_loft.mem_nhds hp) |>.pow 2).congr_of_eventuallyEq ?_
    filter_upwards [open_loft.mem_nhds hp] with w e; exact if_pos e
  have hg : AnalyticOnNhd ℂ G s :=
    (analyticOnNhd_iff_differentiableOn ho).mpr fun z p=>(hdiff z p).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ F loft := (analyticOnNhd_iff_differentiableOn open_loft).mpr h.straight
  have hconv : Convex ℝ s :=
    (convex_Ioo _ _).linear_preimage Complex.reLm

  let m (r:ℝ) : ℂ := ⟨(a+b)/2, r⟩
  have hm (r:ℝ) : m r ∈ s := (show a < (a+b)/2 ∧ (a+b)/2 < b by constructor <;> linarith)
  have hGG : EqOn G 0 s := hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hconv.isPreconnected (hm (-1)) (by
    have p : (m (-1)).im < 0 := neg_one_lt_zero
    filter_upwards [(continuous_im.tendsto (m (-1))).eventually (gt_mem_nhds p)]
      with w (hw : w.im < 0); exact if_neg (not_lt_of_gt hw))
  have hp : m 1 ∈ loft := zero_lt_one (α:=ℝ)
  refine hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const convLoft hp ?_
  filter_upwards [open_loft.mem_nhds hp, ho.mem_nhds (hm 1)] with w e j
  have hz : F w ^2 = 0 :=
    ((if_pos e : G w = (F w)^2)).symm.trans (hGG j)
  simpa using hz

/-- Analytic uniqueness at positive imaginary translations within an interval. -/
lemma heights (h : Air F C) (ha : 0 ≤ a) (hab : a < b)
    (h0 : ∀ t : ℝ, t ∈ Ioo a b → F ⟨0, t⟩ = 0) :
    EqOn F 0 loft := by
  let f (t : ℝ) : ℂ := ⟨0, t⟩
  let m := (a+b)/2
  have hm : m ∈ Ioo a b := ⟨by unfold m; linarith, by unfold m; linarith⟩
  have p : f m ∈ loft := lt_of_le_of_lt ha hm.1
  have hc : Continuous f := by
    convert continuous_ofReal.mul (continuous_const (y:=I)) using 1
    funext; apply Complex.ext <;> simp [f]
  have he : Tendsto f (𝓝[≠] m) (𝓝[≠] (f m)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hc.tendsto m).mono_left nhdsWithin_le_nhds,
      Eventually.mono self_mem_nhdsWithin fun x (r:x≠m) (k:f x=f m)=>r (congrArg Complex.im k)⟩
  exact ((analyticOnNhd_iff_differentiableOn open_loft).mpr h.straight
    ).eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const convLoft p
      (he.frequently ((((Filter.eventually_mem_set.mpr (isOpen_Ioo.mem_nhds hm)).filter_mono nhdsWithin_le_nhds).mono
         fun t u=>h0 t u).frequently))

end Air

variable {H : Hilbert} {a : Axis} (S : Semigroup H a)

lemma J_lift (v : H) (w : S.muslin) :
    ∃ D ≥ (0:ℝ), ∀ z : ℂ, 0 ≤ z.im →
      ‖S.J 0 v w.val z - S.J 0 v w.val z.re‖ ≤ D * z.im := by
  obtain ⟨w', h⟩ := S.muslin_exhibit w 1
  rw [pow_one] at h
  refine ⟨‖v‖ * 2 * ‖w'‖, by positivity, fun z hz=>?_⟩
  rw [J,J,←inner_sub_right]
  refine (norm_inner_le_norm v _).trans ?_
  rw [ray,ray,Complex.ofReal_re,Complex.ofReal_im,← map_sub,S.unit.unitary, ← map_sub,S.life]
  rw [Real.toNNReal_zero,S.eZero,ContinuousLinearMap.id_apply,
      ← h, norm_sub_rev, ← mul_apply_eq_comp, ← sub_apply]
  refine (mul_le_mul_of_nonneg_left (((S.gauze - S.E z.im.toNNReal*S.gauze).le_opNorm w').trans
     (mul_le_mul_of_nonneg_right (gauze_tug S _) (norm_nonneg _))) (norm_nonneg _)).trans_eq ?_
  rw [Real.coe_toNNReal _ hz]; ring

/-- Move joint discrepancy to the real edge while staying in ANY strictly
funded time range; includes a positive-heat hypothesis with phase adjustment. -/
theorem paid_move_real {v : H} {w : S.muslin} {T : ℝ≥0} (u : 0 < T)
    {t : ℝ} (p : inner ℂ v (S.edge t (S.E T w.val)) ≠ 0)
    {l r : ℝ} (y : l < r) :
    ∃ s ∈ Ioo l r, inner ℂ v (S.unit.translation (s • basis a) w.val) ≠ 0 := by
  by_contra! e
  have h0 : ∀ s ∈ Ioo l r, S.J 0 v w.val s = 0 := by
    intro s hs; rw [veers,zero_add]; exact e s hs
  obtain ⟨D,d,f⟩ := J_lift S v w
  have hv := Air.squared_interval (S.altitude 0 v w.val) f y d h0
  apply p
  simpa only [J,ray,S.unit.origin,ContinuousLinearMap.id_apply,Real.toNNReal_coe,
     Pi.zero_apply] using (hv (show (⟨t, T⟩ : ℂ) ∈ loft from u))

/-- Pull shorter strictly positive duration out of a longer bill. -/
theorem paid_move_heat {v w : H} {T : ℝ≥0} (u : 0 < T)
    (p : inner ℂ v (S.E T w) ≠ 0)
    {l r : ℝ} (x : 0 ≤ l) (y : l < r) :
    ∃ t : ℝ≥0, (t:ℝ) ∈ Ioo l r ∧ inner ℂ v (S.E t w) ≠ 0 := by
  by_contra! e
  have h0 : ∀ t : ℝ, t ∈ Ioo l r → S.J 0 v w ⟨0,t⟩ = 0 := by
    intro t ht
    have hs := Real.coe_toNNReal t (show 0 ≤ t from le_trans x ht.1.le)
    have hr := e t.toNNReal (hs.symm ▸ ht)
    exact by simpa only [J,ray,S.unit.origin,S.birth,ContinuousLinearMap.id_apply] using hr
  have hv := Air.heights (S.altitude 0 v w) x y h0
  apply p
  exact by simpa only [J,ray,S.unit.origin,ContinuousLinearMap.id_apply,Real.toNNReal_coe,S.birth,
     Pi.zero_apply] using (hv (show (⟨0, T⟩ : ℂ) ∈ loft from u))

end Gingham
end YM.OS.Semigroup

