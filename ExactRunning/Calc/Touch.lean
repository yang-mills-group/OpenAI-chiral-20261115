import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Second order contact on scalar rays. -/

set_option autoImplicit false
noncomputable section
open Asymptotics Filter Set
open scoped ContDiff Topology BigOperators

namespace ExactRunning
variable {E : Type*} [NormedAddCommGroup E]

/-- Second order contact at 0. Convenience includes continuity. -/
structure Touch (f g : ℝ → E) : Prop where
  hf : ContinuousAt f 0
  hg : ContinuousAt g 0
  small : (fun t => f t - g t) =o[𝓝 0] fun t : ℝ => t ^ 2

namespace Touch
variable {f g h i : ℝ → E}
lemma refl (hf : ContinuousAt f 0) : Touch f f :=
  ⟨hf, hf, (isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm⟩

lemma const (a : E) : Touch (fun _ => a) (fun _ => a) := refl continuousAt_const

lemma zero (h : Touch f g) : f 0 = g 0 := by
  have hp : ‖f 0 - g 0‖ ≤ 1 * ‖(0:ℝ)^2‖ :=
    (h.small.def zero_lt_one).self_of_nhds
  simpa [sub_eq_zero] using hp

@[symm] lemma symm (h : Touch f g) : Touch g f :=
  ⟨h.hg,h.hf,(h.small.neg_left).congr_left fun _ => neg_sub ..⟩

@[trans] lemma trans (a : Touch f g) (b : Touch g h) : Touch f h :=
  ⟨a.hf,b.hg,(a.small.add b.small).congr_left fun _ => sub_add_sub_cancel ..⟩

lemma congr {f' g' : ℝ → E} (h : Touch f g) (hf : f =ᶠ[𝓝 0] f') (hg : g =ᶠ[𝓝 0] g') :
    Touch f' g' :=
  ⟨h.hf.congr_of_eventuallyEq hf.symm,h.hg.congr_of_eventuallyEq hg.symm,h.small.congr' (hf.sub hg) .rfl⟩

lemma add (a : Touch f g) (b : Touch h i) :
    Touch (fun t => f t + h t) (fun t => g t + i t) :=
  ⟨a.hf.add b.hf, a.hg.add b.hg, (a.small.add b.small).congr_left fun _ => by abel⟩

lemma neg (h : Touch f g) :
    Touch (fun t => -(f t)) (fun t => -(g t)) :=
  ⟨h.hf.neg,h.hg.neg,h.small.neg_left.congr_left fun _ => by abel⟩

lemma sub (a : Touch f g) (b : Touch h i) :
    Touch (fun t => f t - h t) (fun t => g t - i t) := by
  simp only [sub_eq_add_neg]
  exact a.add b.neg

lemma sum {ι : Type*} {s : Finset ι} {f g : ι → ℝ → E} (h : ∀ j ∈ s, Touch (f j) (g j)) :
    Touch (fun t => ∑ j ∈ s,f j t) (fun t => ∑ j ∈ s,g j t) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using const (0:E)
  | @insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    exact (h _ (Finset.mem_insert_self ..)).add (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

lemma smul {𝕜 : Type*} [NormedRing 𝕜]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {u v : ℝ → 𝕜}
    (a : Touch u v) (b : Touch f g) :
    Touch (fun t => u t • f t) (fun t => v t • g t) := by
  refine ⟨a.hf.smul b.hf, a.hg.smul b.hg, ?_⟩
  have := (a.small.smul_isBigO (b.hf.tendsto.isBigO_one ℝ))
  refine ((this.add ((a.hg.tendsto.isBigO_one ℝ).smul_isLittleO b.small |>.congr_right (by intro; simp)))).congr ?_ ?_
  · intro x; simp only [smul_sub,sub_smul]; abel
  intro x; simp

lemma mul {R : Type*} [NormedRing R] {f g h i : ℝ → R} (a : Touch f g) (b : Touch h i) :
    Touch (fun t => f t * h t) (fun t => g t * i t) := a.smul b

lemma prod {ι R : Type*} [NormedCommRing R] {s : Finset ι} {f g : ι → ℝ → R} (h : ∀ j ∈ s, Touch (f j) (g j)) :
    Touch (fun t => ∏ j ∈ s,f j t) (fun t => ∏ j ∈ s,g j t) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using const (1:R)
  | @insert x s hx ih =>
    simp only [Finset.prod_insert hx]
    exact (h _ (Finset.mem_insert_self ..)).mul (ih (fun j hj => h _ (Finset.mem_insert_of_mem hj)))

variable [NormedSpace ℝ E]
lemma app {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (a : Touch f g) (h : ContDiffAt ℝ 1 u (f 0)) :
    Touch (fun t => u (f t)) (fun t => u (g t)) := by
  have h' := h; rw [a.zero] at h'
  refine ⟨h.continuousAt.comp a.hf,h'.continuousAt.comp a.hg,?_⟩
  obtain ⟨K,s,hs,hk⟩ := (h.hasStrictFDerivAt (by simp)).exists_lipschitzOnWith
  have hg : s ∈ 𝓝 (g 0) := a.zero ▸ hs

  refine IsBigO.trans_isLittleO (IsBigO.of_bound K ?_) a.small
  filter_upwards [a.hf hs, a.hg hg] with t ht hu
  exact hk.norm_sub_le ht hu

lemma log {f g : ℝ → ℝ} (a : Touch f g) (h : f 0 ≠ 0) :
    Touch (fun t => Real.log (f t)) (fun t => Real.log (g t)) :=
  a.app (Real.contDiffAt_log.2 h)
end Touch

variable [NormedSpace ℝ E]
/-- Second coefficient with factorial already divided out. -/
def quad (f : ℝ → E) := (2⁻¹:ℝ) • iteratedFDeriv ℝ 2 f 0 1

lemma touch_quad {f : ℝ → E} (h : ContDiffAt ℝ 2 f 0) :
    Touch f (fun t => f 0 + t • deriv f 0 + t^2 • quad f) := by
  obtain ⟨u,hu,hf⟩ := h.contDiffOn (m:=2) le_rfl (by simp)
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.1 hu
  have h0 : (0:ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have ho := Metric.isOpen_ball (x:=(0:ℝ)) (ε:=r)
  have hlt := taylor_isLittleO (n:=2) (convex_ball _ r) h0 (hf.mono he)
  rw [ho.nhdsWithin_eq h0] at hlt
  refine ⟨h.continuousAt, ?_, hlt.congr ?_ (by intro; simp)⟩
  · fun_prop
  intro t
  congr 1
  rw [show 2=0+1+1 by rfl, taylorWithinEval_succ,taylorWithinEval_succ,taylor_within_zero_eval,
    iteratedDerivWithin_of_isOpen ho h0,iteratedDerivWithin_of_isOpen ho h0]
  norm_num [iteratedDeriv_one,quad,Nat.factorial,← mul_smul]
  rw [mul_comm,iteratedDeriv_eq_iteratedFDeriv]
  rfl

lemma Touch.deriv_eq {f g : ℝ → E} (h : Touch f g) (hf : DifferentiableAt ℝ f 0)
    (hg : DifferentiableAt ℝ g 0) : deriv f 0 = deriv g 0 := by
  have hz : HasDerivAt (fun t => f t - g t) 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    simpa [h.zero] using h.small.trans (isLittleO_pow_pow (by decide : 1 < 2))
  exact sub_eq_zero.1 ((hf.hasDerivAt.sub hg.hasDerivAt).unique hz)

lemma Touch.quad_eq {f g : ℝ → E} (h : Touch f g) (hf : ContDiffAt ℝ 2 f 0)
    (hg : ContDiffAt ℝ 2 g 0) : quad f = quad g := by
  have hx := (((touch_quad hf).symm.trans h).trans (touch_quad hg)).small
  rw [h.zero,h.deriv_eq (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))] at hx
  have ht : (fun t : ℝ => t^2 • (quad f - quad g)) =o[𝓝[≠] 0] fun t => t ^ 2 := by
    simpa [smul_sub] using hx.mono (nhdsWithin_le_nhds (s:={0}ᶜ))
  by_contra he
  have hu : 0 < ‖quad f - quad g‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  obtain ⟨t,h1,h2⟩ := (eventually_mem_nhdsWithin.and (ht.def (half_pos hu))).exists
  have h1 : t ≠ 0 := h1
  rw [norm_smul,mul_comm _ ‖t ^ 2‖] at h2
  exact not_le_of_gt (mul_lt_mul_of_pos_left (half_lt_self hu) (norm_pos_iff.2 (pow_ne_zero _ h1))) h2
end ExactRunning
