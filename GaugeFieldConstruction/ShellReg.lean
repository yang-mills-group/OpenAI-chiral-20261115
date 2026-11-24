/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.ShellWork

/-!
# Local charge using one smooth source regularization
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux
open Gap Complex Function Filter Set YM.Analysis MeasureTheory
open YM.Maxwell YM.Maxwell.Free
open scoped Topology BigOperators ContDiff
variable {U : Set E4} {χ : E4→ℝ}

-- replace real testing_source proof with vector
lemma tour {f : FunC} (hf : Continuous f) (hc : HasCompactSupport f) (x : E4) :
    Tendsto (fun t=> ∫ y:E4, source t (y-x) • f y) (𝓝[>] (0:ℝ)) (𝓝 (f x)) := by
  have he t (ht :0<t): (∫ y:E4, source t (y-x) • f y)= ∫ y:E4, source 1 y • f (x+t • y) := by
    rw [dilate_integral _ x t ht,← integral_smul]
    apply integral_congr_ae; refine Eventually.of_forall fun y=>?_
    simp only [add_sub_cancel_left, smul_smul, source_scale ht]
  obtain ⟨C,hC⟩:= hf.bounded_above_of_compact_support hc
  have hv : (∫ y:E4,source 1 y • f x)=f x := by rw [integral_smul_const,source_profile.2,one_smul]
  apply Tendsto.congr' ?_ (show Tendsto (fun t:ℝ=>∫ y:E4, source 1 y • f (x+t • y)) _ _ from ?_)
  · filter_upwards [self_mem_nhdsWithin] with t ht; exact (he t ht).symm
  rw [← hv]
  apply tendsto_integral_filter_of_dominated_convergence (fun y=>‖source 1 y‖ * C) _ _ (source_profile.1.norm.mul_const C)
  · refine Eventually.of_forall fun y=>?_
    have h : Continuous (fun t : ℝ=> source 1 y • f (x+t • y)) := (continuous_const (y:=source 1 y)).smul (hf.comp (show Continuous fun t : ℝ=> x+t • y by fun_prop))
    simpa using (h.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi 0))
  · exact Eventually.of_forall fun t=> ((source_diff (by norm_num : (0:ℝ)<1)).continuous.smul (hf.comp (show Continuous fun y:E4=>x+t • y by fun_prop))).aestronglyMeasurable
  refine Eventually.of_forall fun t=> Eventually.of_forall fun y=>?_
  change ‖_ • f _‖ ≤ _; rw [norm_smul]; gcongr; exact hC _

/-- Real source function σ approximation centered at x. -/
def soul (t : ℝ) (x y : E4):=source t (y-x)
lemma tune {t : ℝ} (h : 0<t) (x) : ContDiff ℝ ∞ (soul t x) := ((source_diff h).comp (f:= fun z=>z-x) (contDiff_id.sub contDiff_const)).of_le le_top
lemma remit {f : FunC} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : E4) (a : Axis) :
    Tendsto (fun t=> ∫ y:E4, (grad a (soul t x) y:ℝ) • f y) (𝓝[>] (0:ℝ)) (𝓝 (-grad a f x)) := by
  have hd : ContDiff ℝ ∞ (grad a f) := contDiff_iff_contDiffAt.mpr (fun u=>grad_smooth a hf.contDiffAt (by simp))
  have hh :HasCompactSupport (grad a f) := hc.fderiv_apply ℝ _
  apply (tour hd.continuous hh x).neg.congr'; filter_upwards [self_mem_nhdsWithin] with t ht
  change - (∫ y:E4,soul t x y • grad a f y)=∫ y:E4,(grad a (soul t x) y:ℝ) • f y
  have h:= tune (show 0<t from ht) x
  have he : Integrable (fun y=>soul t x y • grad a f y):= (h.continuous.smul hd.continuous).integrable_of_hasCompactSupport hh.smul_left
  have hu :Integrable (fun y=>soul t x y • f y):= (h.continuous.smul hf.continuous).integrable_of_hasCompactSupport hc.smul_left
  have hv : Integrable (fun y=> (grad a (soul t x) y:ℝ) • f y):= ((gradient_smooth h a).continuous.smul hf.continuous).integrable_of_hasCompactSupport hc.smul_left
  have H: (∫ y:E4,soul t x y • grad a f y)= -(∫ y:E4,(grad a (soul t x) y:ℝ) • f y):= integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hv he hu
    (fun u _=> h.differentiable (by simp) u) (fun u _=> hf.differentiable (by simp) u)
  rw [H,neg_neg]

lemma glow {f : FunC} (B : Cost χ) (h :∀ x∈tsupport χ, ContDiffAt ℝ ∞ f x):
    ContDiff ℝ ∞ (fun z=>χ z • f z) := by
  apply contDiff_iff_contDiffAt.mpr; intro x; by_cases v:x∈ tsupport χ
  · exact B.health.contDiffAt.smul (h x v)
  apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp v] with y hy; change χ y • f y= _; rw [show χ y=0 from hy,zero_smul]

/-- regulate with the tested divergence only in *support*. -/
theorem rates (B : Cost χ) (x : E4) (C : χ =ᶠ[𝓝 x] fun _=>1) (j : ℝ → Jobs) (f : FunC) (g : Jobs)
    (hf : ∀ z∈tsupport χ,ContDiffAt ℝ ∞ f z) (hg : ∀ i z, z∈ tsupport χ → ContDiffAt ℝ ∞ (g i) z)
    (ct : Continuous fun t : ℝ=> Flux χ (j t))
    (K : ∀ t : ℝ,0<t → ∀ i z,z∈ tsupport χ→ContDiffAt ℝ ∞ (j t i) z)
    (D : ∀ t : ℝ,0<t → ∀ z∈tsupport χ,sumD (j t) z = (soul t x z) • f z + ∑ i : Axis,(grad i (soul t x) z:ℝ) • g i z):
    Flux χ (j 0)=sumD g x-f x := by
  let F:=fun z=> χ z • f z; let G (i : Axis) z:= χ z • g i z
  have hr := tour (glow B hf).continuous (show HasCompactSupport F from B.compact.smul_right) x
  have ht (i) := remit (glow B (hg i)) (show HasCompactSupport (G i) from B.compact.smul_right) x i
  have hd : F x=f x := by unfold F; rw [show χ x=1 from C.self_of_nhds,one_smul]
  have he (a i) : grad a (G i) x= grad a (g i) x := by
    apply GermD; filter_upwards [C] with y hy; change χ y • _ = _; rw [show χ y=1 from hy,one_smul]
  refine tendsto_nhds_unique (ct.continuousAt.continuousWithinAt (x:=0) (s:=Ioi 0)) ?_
  have h: -(F x + ∑ i : Axis, (-grad i (G i) x))=sumD g x-f x := by simp only [he, Finset.sum_neg_distrib,sumD,hd]; abel
  rw [← h]; apply (hr.add (tendsto_finsetSum _ (fun i _=>ht i))).neg.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hT : 0 < t := ht
  rw [across B (K t hT)]
  congr 1
  let v i y:=grad i (soul t x) y • G i y
  have p (i : Axis) : Integrable (v i):= ((gradient_smooth (tune hT x) i).continuous.smul (glow B (hg i)).continuous).integrable_of_hasCompactSupport (show HasCompactSupport (G i) from B.compact.smul_right).smul_left
  have u: Integrable (fun y=> soul t x y • F y) := ((tune hT x).continuous.smul (glow B hf).continuous).integrable_of_hasCompactSupport (show HasCompactSupport F from B.compact.smul_right).smul_left
  change (∫ y:E4,soul t x y • F y)+(∑ i:Axis,∫ y:E4, v i y)=_
  rw [← integral_finsetSum Finset.univ (fun i _=>p i),← integral_add u (integrable_finsetSum _ (fun i _=>p i))]
  refine integral_congr_ae (Eventually.of_forall fun y=>?_)
  by_cases hv : y ∈ tsupport χ
  · simp only [D t hT y hv,F,G,v, Finset.smul_sum,smul_add]; rw [smul_comm (χ y)]; congr 1; exact Finset.sum_congr rfl (fun i _=> smul_comm _ _ _)
  simp [F,G,v,image_eq_zero_of_notMem_tsupport hv]
end YM.GaugeFieldConstruction.Flux
