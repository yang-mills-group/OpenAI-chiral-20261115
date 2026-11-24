import YM.SU5.Cheer.Sonnet
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyConvergence
set_option autoImplicit false
set_option maxHeartbeats 260000
/-! # Complex extension through the edge (values, not derivatives). And a weak-* theorem! -/
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex MeasureTheory Measure Mink
open scoped Real Topology NNReal ENNReal InnerProductSpace BigOperators
variable (μ ν : Narrow) (e t:ℝ≥0)(p:Space3)(x:ℂ)(F:ℕ→Narrow)
local notation "M"=> Measure E4
local notation "t'"=> ((t:ℝ):ℂ)
local notation "σ"=> tendsK p x
private lemma entry (E:E4): tendsK 0 (t':ℂ) E=↑(Real.exp (- ((t:ℝ)*time E))):=by unfold tendsK; push_cast; simp only [inner_zero_right,ofReal_zero,zero_mul,zero_sub]
private lemma spinUp (E:E4): tendsK p (x+t') E = σ E * tendsK 0 t' E:=by unfold tendsK; rw [← Complex.exp_add]; simp only [inner_zero_right, ofReal_zero,zero_mul]; ring_nf
-- comparisons on closed half periphery
variable (h:Brilliant μ)(u:0≤ x.re)
def tab (t:ℝ≥0) (μ:Narrow):ℝ := (μ.mass:ℝ)-(FLap μ 0 (t:ℝ)).re
include h u
lemma deflate : ‖FLap μ p x - FLap μ p (x+t')‖ ≤ tab t μ:=by
 let K: E4→ℝ:= fun E=> 1-Real.exp (-((t:ℝ)*time E)); have he:∀ E, K E=((tendsK 0 0 E).re)-(tendsK 0 (t:ℝ) E).re:=fun E=>by rw [entry,ofReal_re]; unfold K tendsK; simp
 have hZ : 0≤(t').re:=t.property; have ht: Integrable K (μ:M) := by
    have ht1:=destined μ 0 _ h hZ; have ht2:= destined μ 0 0 h (show (0:ℝ)≤(0:ℂ).re from le_rfl)
    simp_rw [show K=fun E=> RCLike.re (tendsK 0 0 E)-RCLike.re (tendsK 0 (t:ℝ) E) from funext he]; exact ht2.re.sub ht1.re
 unfold FLap; rw [← integral_sub (destined μ p _ h u) (destined μ p _ h (show 0 ≤ (x+t').re from add_nonneg u hZ))]
 -- leaves h? tune
 refine (norm_integral_le_integral_norm _).trans ?_
 have hb:Integrable (fun E=>σ E-tendsK p (x+t') E) (μ:M) := (destined μ p x h u).sub (destined μ p _ h (add_nonneg u hZ))
 refine (integral_mono_ae hb.norm ht (Eventually.mono h fun i v=>?_)).trans_eq ?_
 · simp only [spinUp,entry]; rw [show σ i-σ i *↑(Real.exp (-((t:ℝ)*time i)))= σ i * ↑(K i) by unfold K; push_cast; ring, norm_mul,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ K i from sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg t.property v))))]; exact mul_le_of_le_one_left (by exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg t.property v)))) (withinK _ _ i u v)
 have ht1:=destined μ 0 _ h hZ; have ht2:= destined μ 0 0 h (show (0:ℝ)≤(0:ℂ).re from le_rfl)
 simp_rw [he]; unfold tab; change (∫ v, RCLike.re (tendsK 0 0 v) - RCLike.re (tendsK 0 t' v) ∂(μ:M))= _; rw [integral_sub ht2.re ht1.re,integral_re ht2,integral_re ht1]; change (FLap μ 0 0).re - _ = _; rw [launched_z]; rfl
private def rowK (t : ℝ≥0) := x + ((t:ℝ):ℂ)
private lemma tent (s:ℝ≥0): AEStronglyMeasurable (tendsK p (rowK x s)) (μ:M):= (airy p (rowK x s)).aestronglyMeasurable
private lemma pick (s:ℝ≥0): ∀ᵐ z ∂(μ:M), ‖tendsK p (rowK x s) z‖ ≤1:= by
 have hv:0≤ (rowK x s).re:= by unfold rowK; simp only [add_re,ofReal_re]; exact _root_.add_nonneg u s.property
 exact Eventually.mono h (fun i q => withinK p (rowK x s) i hv q)
private lemma owned : Continuous (fun t=> ∫ i, tendsK p (rowK x t) i ∂(μ:M)):= by
 apply continuous_of_dominated (μ:=(μ:M)) (F:=fun (s:ℝ≥0)=> tendsK p (rowK x s)) (fun s=> tent μ p x h u s) (bound:=fun _=>1) (pick μ p x h u) (integrable_const (1:ℝ)) (ae_of_all _ (fun i=>?_))
 unfold tendsK rowK; fun_prop
lemma coast : Continuous (fun t:ℝ≥0=> FLap μ p (rowK x t)):= owned μ p x h u
namespace Lyrical
variable{μ F}(A:Lyrical μ F)
omit h
include A
lemma val : Tendsto (fun i=> FLap (F i) p x) atTop (𝓝 (FLap μ p x)):=by
 apply Metric.tendsto_nhds.mpr; intro ε e
 let G(s:ℝ≥0):=tab s μ; have hz:G 0=0:=by simp [G,tab,launched_z]
 have hv:Continuous G:=by
    have hv:= coast μ 0 0 A.bright (show (0:ℝ)≤(0:ℂ).re from le_rfl); simp only [rowK,zero_add] at hv; exact continuous_const.sub (Complex.continuous_re.comp hv)
 let q:=ε/3; have he:0<q:=by unfold q; positivity
 have hw:= ((hv.continuousAt.tendsto.eventually (gt_mem_nhds (show G 0 < q by rwa [hz]))).filter_mono (nhdsWithin_le_nhds (s:=Ioi (0:ℝ≥0)))) -- tune
 obtain ⟨t,H,p'⟩:= (hw.and (self_mem_nhdsWithin (s:=Ioi (0:ℝ≥0)))).exists
 let y:= (x+↑(t:ℝ)); have hy: 0<y.re:= add_pos_of_nonneg_of_pos u p'
 have hT: Tendsto (fun i=>tab t (F i)) atTop (𝓝 (tab t μ)):= A.massR.sub (Complex.continuous_re.continuousAt.tendsto.comp (A.meets 0 t))
 filter_upwards [hT.eventually (gt_mem_nhds H),Metric.tendsto_nhds.mp (A.voices p y hy) q he] with i h v
 change dist _ (FLap μ p y)< q at v; change tab t _ < _ at h H
 have hB:= (deflate (F i) t p x (A.there i) u).trans_lt h; have hC:= (deflate μ t p x A.bright u).trans_lt H
 rw [← dist_eq_norm] at hB hC; change dist _ (FLap (F i) p y) < _ at hB; change dist _ (FLap μ p y)< _ at hC; rw [dist_comm] at hC
 grw [dist_triangle (FLap (F i) p x) (FLap (F i) p y),dist_triangle (FLap (F i) p y) (FLap μ p y) (FLap μ p x),hC]; unfold q at *; linarith -- tune
omit A u in
lemma lays_flat (μ:Narrow)(b:E4): charFun (μ:M) b = FLap μ (spatial b) (-(time b:ℂ)*I):=by
 unfold FLap; rw [charFun_apply]; apply integral_congr_ae (ae_of_all _ fun i=>?_); unfold tendsK; rw [Mink.pairing]; push_cast; ring_nf
omit u
lemma shone (b:E4): Tendsto (fun i=>charFun (F i:M) b) atTop (𝓝 (charFun (μ:M) b)):= by simp_rw [show ∀ θ:Narrow,charFun (θ:M) b= _ from (fun θ=> lays_flat _ b)]; exact A.val _ _ (by simp)
lemma march (g:(μ:M)≠0): Tendsto F atTop (𝓝 μ):= by
 have hg:μ≠0:= fun h=> by rw [h] at g; exact g rfl
 let α(i:ℕ):= (F i).normalize; have hM:Tendsto (fun i=>(F i).mass) atTop (𝓝 μ.mass):=by exact (tendsto_subtype_rng.mpr A.massR)
 refine (FiniteMeasure.tendsto_normalize_iff_tendsto hg).mp ⟨ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr (fun b=>?_),hM⟩
 have ht(r:Narrow)(hr:r≠0): charFun (r.normalize:M) b= ((r.mass:ℝ):ℂ)⁻¹ * charFun (r:M) b:= by rw [r.toMeasure_normalize_eq_of_nonzero hr,charFun_apply,charFun_apply]; simp [NNReal.smul_def,Complex.real_smul]
 have hf: (μ.mass:ℝ) ≠0:= by exact_mod_cast μ.mass_nonzero_iff.mpr hg
 rw [ht _ hg]; refine (((Complex.continuous_ofReal.continuousAt.tendsto.comp A.massR).inv₀ (ofReal_ne_zero.mpr hf)).mul (A.shone b)).congr' ?_; filter_upwards [hM.eventually_ne (μ.mass_nonzero_iff.mpr hg)] with i h; exact (ht _ ((F i).mass_nonzero_iff.mp h)).symm
end Lyrical
end YM.Cheer
#print axioms YM.Cheer.Lyrical.val
#print axioms YM.Cheer.Lyrical.march
