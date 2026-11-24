import ExactRunning.Calc.Touch
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Agreement through fourth order and contact of Hessians
-/
namespace ExactRunning
noncomputable section
open scoped Topology ContDiff
variable {E F H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup H]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ H]

structure Tandem (n : ℕ) (f g : E → F) : Prop where
  hf : ContDiffAt ℝ ω f 0
  hg : ContDiffAt ℝ ω g 0
  same : ∀ i ≤ n, iteratedFDeriv ℝ i f 0 = iteratedFDeriv ℝ i g 0

namespace Tandem
variable {n : ℕ} {f g : E → F}

lemma pre (h : Tandem n f g) {k : H → E} (hk : ContDiffAt ℝ ω k 0) (h0 : k 0=0) :
    Tandem n (f ∘ k) (g ∘ k) := by
  have hf : ContDiffAt ℝ ω f (k 0) := h0.symm ▸ h.hf
  have hg : ContDiffAt ℝ ω g (k 0) := h0.symm ▸ h.hg
  refine ⟨hf.comp _ hk,hg.comp _ hk,fun i hi => ?_⟩
  rw [iteratedFDeriv_comp hf hk le_top, iteratedFDeriv_comp hg hk le_top,h0]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl; intro c _
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  simp only [ftaylorSeries, h.same c.length (c.length_le.trans hi)]

lemma congr {f' g' : E → F} (h : Tandem n f g) (hf : f =ᶠ[𝓝 0] f') (hg : g =ᶠ[𝓝 0] g') :
    Tandem n f' g' := by
  refine ⟨h.hf.congr_of_eventuallyEq hf.symm,h.hg.congr_of_eventuallyEq hg.symm,fun i hi =>
    ((hf.iteratedFDeriv ℝ i).eq_of_nhds.symm.trans (h.same i hi)).trans
      (hg.iteratedFDeriv ℝ i).eq_of_nhds⟩

lemma drop_head (h : Tandem (n+1) f g) :
    Tandem n (fderiv ℝ f) (fderiv ℝ g) := by
  refine ⟨h.hf.fderiv_right le_top,h.hg.fderiv_right le_top,fun i hi => ?_⟩
  have := h.same (i+1) (Nat.succ_le_succ hi)
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right,
    Function.comp_apply,Function.comp_apply] at this
  exact LinearIsometryEquiv.injective _ this

lemma value (h : Tandem n f g) : f 0 = g 0 := by
  simpa using DFunLike.congr_fun (h.same 0 (Nat.zero_le _)) (![])

lemma touch {f g : ℝ → E} (h : Tandem 2 f g) : Touch f g := by
  refine (touch_quad (h.hf.of_le le_top)).trans (g:=_) ((Touch.trans ?_
      (touch_quad (h.hg.of_le le_top)).symm))
  have h₁ := (drop_head (n:=1) h).value
  have h₂ := h.same 2 le_rfl
  rw [quad,h₂,h.value,deriv,deriv,h₁]
  exact Touch.refl (touch_quad (h.hg.of_le le_top)).hg


lemma bend_in (i : E →L[ℝ] F) {p : F → H} {x : E} (h : ContDiffAt ℝ ω p (i x)) (n : ℕ) :
    iteratedFDeriv ℝ n (p ∘ i) x = (iteratedFDeriv ℝ n p (i x)).compContinuousLinearMap (fun _ => i) := by
  obtain ⟨s,hs,hh⟩ := h.contDiffOn le_top (by intro; rfl) (m:=ω)
  obtain ⟨t,ht,hot,hx⟩ := mem_nhds_iff.mp hs
  have hp := hot.preimage i.continuous
  have hu := i.iteratedFDerivWithin_comp_right (i:=n) (hh.mono ht) hot.uniqueDiffOn hp.uniqueDiffOn hx le_top
  rwa [iteratedFDerivWithin_of_isOpen _ hp hx,
    iteratedFDerivWithin_of_isOpen _ hot hx] at hu

/-- Partial Hessians (second slot) varying with the first slot. -/
lemma hess_touch {f g : E×F → H} (h : Tandem 4 f g) {k : ℝ → E}
    (hk : ContDiffAt ℝ ω k 0) (h0 : k 0 = 0) (v : Fin 2 → F) :
    Touch (fun t => iteratedFDeriv ℝ 2 (fun y => f (k t,y)) 0 v)
          (fun t => iteratedFDeriv ℝ 2 (fun y => g (k t,y)) 0 v) := by
  let d : ℝ → E×F := fun t => (k t,0)
  let i := ContinuousLinearMap.inr ℝ E F
  let a := i (v 0)
  let b := i (v 1)
  have h0 : d 0=0 := Prod.ext h0 rfl
  have hp := pre (drop_head (n:=2) <| drop_head (n:=3) h)
    (k:=d) (hk.prodMk contDiffAt_const) h0 |>.touch
  let L := (ContinuousLinearMap.apply ℝ H b).comp (ContinuousLinearMap.apply ℝ (E×F →L[ℝ] H) a)
  have hd := hp.app (u:=L) (by apply ContDiff.contDiffAt; apply ContinuousLinearMap.contDiff)
  have hx (z : E×F → H) (hz : ContDiffAt ℝ ω z 0) :
      (fun t => L (fderiv ℝ (fderiv ℝ z) (d t))) =ᶠ[𝓝 0]
      fun t => iteratedFDeriv ℝ 2 (fun y => z (k t,y)) 0 v := by
    have ht : Filter.Tendsto d (𝓝 0) (𝓝 0) := by
      rw [← h0]; exact (hk.prodMk contDiffAt_const).continuousAt
    filter_upwards [ht.eventually (hz.eventually (by simp))] with t hh
    have hw : ContDiffAt ℝ ω (fun x => z (d t + x)) (i (0:F)) :=
      ContDiffAt.comp _ (by simpa only [map_zero,add_zero]) (f:=fun x => d t + x) (contDiffAt_const.add contDiffAt_id)
    rw [show (fun y:F => z (k t,y)) = (fun x => z (d t + x)) ∘ i from by funext; simp [d,i]]
    rw [bend_in i hw,ContinuousMultilinearMap.compContinuousLinearMap_apply,map_zero,iteratedFDeriv_comp_add_left, add_zero,
        iteratedFDeriv_two_apply]
    rfl
  exact hd.congr (hx _ h.hf) (hx _ h.hg)

end Tandem
end
end ExactRunning
