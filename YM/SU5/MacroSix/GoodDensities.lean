import YM.SU5.MacroSix.TestDensity
import YM.SU5.MacroSix.Success
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
/-! # Independent smears with matrix success, including nonnegativity/integral and
specified costs. The nonzero joint result is not inferred by reusing a single test for
both; every application to the external system is literally a product density. -/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Function Finset Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff

variable {I : Type} [Fintype I]
local notation "X" => (I → ℝ)

lemma density_bump (x : X) (ε : ℝ) (p : 0 < ε) : ∃ f : X → ℝ, SmoothDensity f ∧
    tsupport f ⊆ ball x ε := by
  let T : ContDiffBump x := ⟨ε/4,ε/2,by positivity,by linarith⟩
  refine ⟨T.normed volume,⟨T.contDiff_normed,T.hasCompactSupport_normed,fun _ ↦ T.nonneg_normed _,
    T.integral_normed⟩,?_⟩
  rw [T.tsupport_normed_eq]; exact closedBall_subset_ball (by exact half_lt_self p)
lemma densityRoom (U : Set X) (p : U.Nonempty) (v : IsOpen U) : ∃ f : X → ℝ,
    SmoothDensity f ∧ tsupport f⊆ U := by
  obtain ⟨x,h⟩ := p
  obtain ⟨ε,e,d⟩ := Metric.isOpen_iff.mp v _ h
  obtain ⟨f,p,f'⟩ := density_bump x ε e; exact ⟨f,p,f'.trans d⟩

lemma SmoothDensity.integrable {f : (I→ℝ) → ℝ} (p : SmoothDensity f) : Integrable f :=
  p.smooth.continuous.integrable_of_hasCompactSupport p.compact

abbrev jointDensity (f g : X → ℝ) (x : X × X) := f x.1 * g x.2
lemma joint_integrable {f g : X → ℝ} (p : SmoothDensity f) (q : SmoothDensity g) :
    Integrable (jointDensity f g) := p.integrable.mul_prod q.integrable
lemma joint_normal {f g : X → ℝ} (p : SmoothDensity f) (q : SmoothDensity g) :
    ∫ x, jointDensity f g x=1 := by
  unfold jointDensity; rw [← p.mass]
  calc _ = (∫ x, f x) * ∫ y, g y := integral_prod_mul f g
       _ = _ := by rw [q.mass,mul_one]

private lemma constant_kernel (c : ℂ) {f g : X → ℝ} (p : SmoothDensity f) (q : SmoothDensity g) :
    ∫ x, (jointDensity f g x) • c = c := by rw [integral_smul_const,joint_normal p q,one_smul]

private lemma pointApprox {f g : X → ℝ} (p : SmoothDensity f) (q : SmoothDensity g) (c : ℂ)
    (K : X → X → ℂ) (hc : Integrable (weightKernel K f g)) (ε : ℝ) (h : 0 < ε)
    (hr : ∀ y∈ tsupport f, ∀ z ∈ tsupport g, dist (K y z) c ≤ ε) :
    dist (independently K f g) c ≤ ε := by
  let u := weightKernel K f g
  let v (x) := (jointDensity f g x) • c
  let u' (i : X×X) := (jointDensity f g i) * ε
  have H : Integrable (jointDensity f g) := joint_integrable p q
  have hv : Integrable v := H.smul_const _
  have hx (i : X×X) : ‖u i-v i‖ ≤ u' i := by
    by_cases b : i.1∈tsupport f
    swap; · have hf : f i.1 = 0 := image_eq_zero_of_notMem_tsupport b; simp [hf,u,v,u',jointDensity,weightKernel]
    by_cases a : i.2∈tsupport g
    swap; · have hg : g i.2=0 := image_eq_zero_of_notMem_tsupport a; simp [hg,u,v,u',jointDensity,weightKernel]
    have he : u i = jointDensity f g i • K i.1 i.2 := by simp [u,weightKernel,jointDensity,Complex.real_smul]
    unfold v u'; rw [he,← smul_sub,norm_smul,Real.norm_of_nonneg (mul_nonneg (p.nonneg _) (q.nonneg _))]
    exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hr _ b _ a)
      (mul_nonneg (p.nonneg _) (q.nonneg _))
  rw [dist_eq_norm]; change ‖(∫ x, u x)-c‖ ≤ ε
  rw [← show (∫ x, v x) = c from constant_kernel _ p q, ← integral_sub hc hv]
  apply le_trans (norm_integral_le_integral_norm _); refine (integral_mono (hc.sub hv).norm
    (H.mul_const ε) hx).trans_eq ?_
  rw [integral_mul_const,joint_normal p q,one_mul]

variable {J : Type*} [Fintype J] [DecidableEq J] (K : (I → ℝ) → (I → ℝ) → Matrix J J ℂ)
variable (A B : Set (I → ℝ))

def response (f g : X → ℝ) := Matrix.of fun j k ↦ independently (fun x y ↦ K x y j k) f g

theorem reliable_pair (x y : X) (p : x∈A) (q : y∈B) (t : IsOpen A) (v : IsOpen B)
    (h : Success (K x y)) (hc : ∀ j k, ContinuousAt (fun x : X × X ↦ K x.1 x.2 j k) (x,y))
    (hi : ∀ f g, SmoothDensity f → tsupport f ⊆ A → SmoothDensity g → tsupport g ⊆ B →
      ∀ j k, Integrable (weightKernel (fun x y ↦ K x y j k) f g)) :
    ∃ f g, SmoothDensity f ∧ tsupport f ⊆ A ∧ SmoothDensity g ∧ tsupport g ⊆ B ∧
      Success (response K f g) := by
  obtain ⟨r,u,e⟩ := Metric.isOpen_iff.mp (t.prod v) (x,y) (show _ ∧ _ from ⟨p,q⟩)
  let ε (i : ℕ) := (1/2:ℝ)^i
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hp (i) : 0 < ε i := by unfold ε; positivity
  let d (i) := min r (ε i)
  choose f hf fS using fun i ↦ density_bump x (d i) (lt_min u (hp i))
  choose g hg gS using fun i ↦ density_bump y (d i) (lt_min u (hp i))
  have hA (i) : tsupport (f i) ⊆ A := fun v p ↦
    (e (a := (v,y)) ((Metric.ball_subset_ball (min_le_left r (ε i)))
      (show (v,y) ∈ ball (x,y) (d i) from (by rw [← ball_prod_same]; exact ⟨fS i p, mem_ball_self (lt_min u (hp i))⟩)))).1
  have hB (i) : tsupport (g i) ⊆ B := fun z p ↦
    (e (a := (x,z)) (Metric.ball_subset_ball (min_le_left r (ε i)) (by
      rw [← ball_prod_same]; exact ⟨mem_ball_self (lt_min u (hp i)),gS i p⟩))).2
  have he (j k : J) : Tendsto (fun i ↦ response K (f i) (g i) j k) atTop (𝓝 (K x y j k)) := by
    refine Metric.tendsto_nhds.mpr ?_; intro t v
    obtain ⟨δ,h,Y⟩ := Metric.mem_nhds_iff.mp ((hc j k).tendsto.eventually
      (show ball (K x y j k) (t/2) ∈ _ from ball_mem_nhds _ (half_pos v)))
    filter_upwards [hε.eventually (gt_mem_nhds h)] with i rL
    -- shadow y avoid
    refine lt_of_le_of_lt (pointApprox (hf i) (hg i) _ (fun x y ↦ K x y j k)
      (hi (f i) (g i) (hf i) (hA i) (hg i) (hB i) j k) (t/2) (half_pos v) ?_) (half_lt_self v)
    intro a s b p
    apply le_of_lt; apply (Y (a := (a,b)))
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball ((min_le_right _ _).trans rL.le) (fS i s),
      ball_subset_ball ((min_le_right _ _).trans rL.le) (gS i p)⟩
  obtain ⟨i,h⟩ := (eventually_success atTop (fun i ↦ response K (f i) (g i)) _ he h).exists
  exact ⟨f i, g i, hf i,hA i,hg i,hB i,h⟩
end YM.MacroSix
#print axioms YM.MacroSix.reliable_pair
