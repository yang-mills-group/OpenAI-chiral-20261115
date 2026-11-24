import YM.CF.Sample.Nook

/-! Partial uniform expectation schemes. Full everywhere integrations, even with dead slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase.Sample
open scoped BigOperators Topology
open MeasureTheory Set Function Filter
variable {K T E : Type*} [TopologicalSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℝ}
structure Gift (v : K →ℝ) (f : K → E) (m : ℝ) : Prop where
  pos (x) : 0 ≤ v x
  bounded (x) (h : v x≠0) : ‖f x‖≤m
  weighted : Continuous (fun x=>v x • f x)
lemma soft {v : K→ℝ} {f : K→E} {m : ℝ} (p : ∀ x,0≤ v x) (h : ∀ x, v x ≠ 0 → ‖f x‖ ≤ m) (g : Continuous v) (e : ∀ x,v x≠0→ContinuousAt f x) : Gift v f m := by
  refine ⟨p,h,continuous_iff_continuousAt.mpr (fun x=>?_)⟩; by_cases k:v x=0
  · unfold ContinuousAt; dsimp only; rw [k,zero_smul,tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _=>norm_nonneg _) (g:=fun y=>v y*m)
    · intro y; by_cases hy:v y=0
      · simp [hy]
      simp only [norm_smul,Real.norm_of_nonneg (p y)]; exact mul_le_mul_of_nonneg_left (h y hy) (p y)
    simpa only [k,zero_mul] using Tendsto.mul_const m (show Tendsto _ _ (𝓝 (v x)) from g.continuousAt)
  exact g.continuousAt.smul (e x k)
lemma Gift.pullGift {A : Type*} [TopologicalSpace A] {v f} (e : Gift (E:=E) (K:=K) v f n) (Y : A→K) (h : Continuous Y) : Gift (v ∘ Y) (f ∘ Y) n := ⟨fun i=>e.pos _,fun i g=>e.bounded _ g,e.weighted.comp h⟩
lemma Gift.face {v : K→ℝ} {g : K→E} (h : Gift v g n) (p : Continuous v) : ContinuousOn g {x|v x≠0} := by
  have he := (p.continuousOn.inv₀ (s:={x|v x≠0}) fun x hx=>hx).smul h.weighted.continuousOn
  apply he.congr; intro x hx; change g x=(v x)⁻¹ • (v x • g x); rw [smul_smul,inv_mul_cancel₀ (show v x≠0 from hx),one_smul]
lemma Gift.family {v : K→ℝ} {g : K→E} (h : Gift v g n) (p : Continuous v) {x : K} (e : v x≠0) : ContinuousAt g x := by
  apply ContinuousWithinAt.continuousAt (s:={x|v x≠0}) (h.face p x (show _ from e)); exact IsOpen.mem_nhds ((isOpen_ne_fun p continuous_const)) e

variable [MeasurableSpace T] [TopologicalSpace T] [CompactSpace T] [T2Space T] [SecondCountableTopology T] [BorelSpace T]
variable {μ : Measure T} [IsProbabilityMeasure μ]
section
variable [CompleteSpace E]
lemma cap_mean (v : T→ℝ) (f : T→E) (e : ∀ x,v x≠0 → ‖f x‖≤n) (k : ∀ x,0≤ v x) (u : Continuous v) (h : Continuous (fun x=>v x • f x)) (p : (∫ x,v x ∂μ)=1) :
    ‖∫ x,v x • f x ∂μ‖ ≤ n := by
  calc
    _ ≤ ∫ x, ‖v x • f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, v x*n ∂μ := integral_mono (net_compact h.norm) (net_compact (u.mul continuous_const)) (fun x=> by
      by_cases a:v x=0
      · simp [a]
      rw [norm_smul,Real.norm_of_nonneg (k x)]; exact mul_le_mul_of_nonneg_left (e x a) (k x))
    _ = n := by rw [integral_mul_const,p,one_mul]
end
-- nested continuous integrals over live subsets (not necessarily locally compact: use continuityAt result on all outer if have compact input only)
variable [FirstCountableTopology K] [LocallyCompactSpace K]
lemma Gift.settled {v : K×T→ℝ} {g : K×T→E} (h : Gift v g n) : Continuous (fun x : K=> ∫ y, v (x,y) • g (x,y) ∂μ) := net_cont _ _ h.weighted
end YM.CF.Phase.Sample
