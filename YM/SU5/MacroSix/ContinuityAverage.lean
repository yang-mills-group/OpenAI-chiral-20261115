import YM.SU5.MacroSix.Grid
import YM.SU5.Aria.Dyad

/-!
# Single-grid quadrature into the continuous sector (abstract principle)

No continuity or even measurability of the unprojected representation is required;
use near-identity Ellis averages only in the proof, not in the actual quadratures.
Key: translating through the *eventual finer meshes*, and an L¹ estimate on the entire
vector function, so no requirement to bound translations on a running growing slab.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MacroSix.Grid
open Filter Function Finset Set MeasureTheory Metric
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators
open YM.CF.Buffered.Afterglow.Tower.Aria

variable {I : Type*} [Fintype I] {G : Type*} [AddCommGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local notation "J" => Cell I
local notation "X" => RealPos I

/-- Conditions for approximating the continuous projection with near-identity shifts.
`δ` is the mesh, `U` the unprojected grid translation representation, `ρ` the
mesh embedding of tick displacements into it, `α` its real parameter values. -/
structure Setup (δ : ℕ → ℝ) (U : G → E →L[ℂ] E) (ρ : ℕ → J → G) (α : G → X) : Prop where
  pos : ∀ i, 0 < δ i
  vanishes : Tendsto δ atTop (𝓝 0)
  act_add : ∀ g h x, U g (U h x)= U (g+h) x
  norm_eq : ∀ g x, ‖U g x‖=‖x‖
  additiveGrid : ∀ i x y, ρ i (x+y)=ρ i x + ρ i y
  placement : ∀ i x, α (ρ i x)=place (δ i) x
  finer : ∀ g, ∀ᶠ i in atTop, ∃ x, ρ i x=g

variable {δ : ℕ → ℝ} {U : G → E →L[ℂ] E} {ρ : ℕ → Cell I → G} {α : G → RealPos I}

def transportSum (δ : ℕ → ℝ) (U : G → E →L[ℂ] E) (ρ : ℕ → J → G) (f : X → E) (i : ℕ) : E :=
  (((δ i)^Fintype.card I:ℝ):ℂ) • ∑ᶠ k, U (ρ i k) (f (place (δ i) k))

local notation "S" => transportSum δ U ρ

variable (t : Setup δ U ρ α)
namespace Setup

include t

lemma finite (i : ℕ) (f : X → E) (p : HasCompactSupport f) :
    (Function.support fun k ↦ U (ρ i k) (f (place (δ i) k))).Finite :=
  (finite_tags_of _ (t.pos i) p).subset fun k h₀ q ↦ h₀ (by dsimp only at q ⊢; rw [q,map_zero])

lemma sum_add (i : ℕ) {f g : X → E} (p : HasCompactSupport f) (q : HasCompactSupport g) :
    S (f+g) i = S f i + S g i := by
  simp_rw [transportSum, Pi.add_apply,map_add]
  rw [finsum_add_distrib (t.finite i f p) (t.finite i g q), smul_add]

lemma sum_sub (i : ℕ) {f g : X → E} (p : HasCompactSupport f) (q : HasCompactSupport g) :
    S (f-g) i=S f i - S g i := by
  simp_rw [transportSum, Pi.sub_apply,map_sub]
  rw [finsum_sub_distrib (t.finite i f p) (t.finite i g q), smul_sub]

omit t in
lemma sum_smul (i : ℕ) (f : X → E) (c : ℂ) :
    transportSum δ U ρ (c • f) i = c • transportSum δ U ρ f i := by
  simp_rw [transportSum, Pi.smul_apply,map_smul, ← smul_finsum]; rw [smul_comm]

lemma shiftActual (g : G) (f : X → E) :
    ∀ᶠ i in atTop, S (U g ∘ f) i = S (fun x ↦ f (x + (-α g))) i := by
  filter_upwards [t.finer g] with i h
  obtain ⟨j,rfl⟩ := h
  unfold transportSum; congr 1
  apply finsum_eq_of_bijective (fun x : J ↦ x+j) ((Equiv.addRight j).bijective)
  intro x
  rw [comp_apply,t.act_add,t.additiveGrid,t.placement,place_add]
  abel_nf

lemma budget_finite (i : ℕ) (f : X → E) (p : HasCompactSupport f) :
    ‖S f i‖ ≤ (δ i)^Fintype.card I • ∑ᶠ k : J, ‖f (place (δ i) k)‖ := by
  let V := (finite_tags_of _ (t.pos i) p).toFinset
  have h : Function.support (fun k ↦ f (place (δ i) k)) ⊆ V := by simp [V]
  have hd := t.pos i
  have he : Function.support (fun k ↦ U (ρ i k) (f (place (δ i) k))) ⊆ V :=
    fun k e ↦ h (fun (p : f (place (δ i) k)=0) ↦ e (by dsimp only; rw [p,map_zero]))
  have hr : Function.support (fun k ↦ ‖f (place (δ i) k)‖) ⊆ V :=
    fun k e ↦ h (fun (p : f (place (δ i) k)=0) ↦ e (by dsimp only; rw [p,norm_zero]))
  rw [transportSum, finsum_eq_sum_of_support_subset _ he, finsum_eq_sum_of_support_subset _ hr,
    norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans (norm_sum_le _ _)
  simp only [t.norm_eq, le_refl]

/-- Eventual estimate for *fixed* vector functions. -/
lemma cost (f : X → E) (p : Continuous f) (q : HasCompactSupport f)
    (c : ℝ) (h : (∫ x, ‖f x‖) < c) : ∀ᶠ i in atTop, ‖S f i‖ < c := by
  filter_upwards [(quadrature _ p.norm q.norm t.pos t.vanishes).eventually (gt_mem_nhds h)] with i k
  exact (t.budget_finite i f q).trans_lt k

-- L¹ shift cost. Need only distance from zero (works before enter E into measurable spaces).
omit t in
private lemma shiftBudget (f : X → E) (p : Continuous f) (q : HasCompactSupport f) :
    Tendsto (fun h : X ↦ ∫ x, ‖f x - f (x + -h)‖) (𝓝 0) (𝓝 0) := by
  obtain ⟨A,h⟩ := (show IsCompact (tsupport f) from q).isBounded.subset_closedBall (0:X)
  obtain ⟨c,u⟩ := p.bounded_above_of_compact_support q
  have hv : 0 ≤ c := (norm_nonneg _).trans (u 0)
  let D := closedBall (0:X) (A+1)
  have hm : MeasurableSet D := Metric.isClosed_closedBall.measurableSet
  let B := D.indicator fun _ ↦ c+c
  have hB : Integrable B := (integrable_indicator_iff hm).mpr (integrableOn_const
    (isCompact_closedBall _ _ |>.measure_lt_top.ne))
  let F (v : X) (x : X) := ‖f x - f (x + -v)‖
  have hx : Tendsto (fun h ↦ ∫ x, F h x) (𝓝 0) (𝓝 (∫ x, F 0 x)) := by
    refine tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall (fun v ↦
      (p.sub (p.comp (continuous_id.add continuous_const))).norm.aestronglyMeasurable))
      ?_ hB (ae_of_all _ (fun x ↦ (show Continuous (fun v ↦ F v x) from
        (continuous_const.sub (p.comp (continuous_const.add continuous_neg))).norm).continuousAt))
    filter_upwards [Metric.ball_mem_nhds (0:X) zero_lt_one] with v Hv
    apply ae_of_all; intro x
    rw [Real.norm_of_nonneg (show 0 ≤ F v x from norm_nonneg _)]
    by_cases e : x∈D
    · rw [show B x=c+c from Set.indicator_of_mem e _]
      exact (norm_sub_le ..).trans (add_le_add (u _) (u _))
    have hz : f x=0 := by
      by_contra k
      exact e (Metric.closedBall_subset_closedBall (by linarith) (h (subset_tsupport f k)))
    have ht : f (x+-v) = 0 := by
      by_contra k
      have he := h (subset_tsupport f k)
      refine e ((dist_triangle _ (x+-v) _).trans ?_)
      have hg : dist x (x+-v) ≤ 1 := by
        simpa using (show dist v 0 ≤ 1 from (show dist v 0 < 1 from Hv).le)
      linarith [Metric.mem_closedBall.mp he]
    simp [F,hz,ht,B,e]
  simpa only [F,neg_zero,add_zero,sub_self,norm_zero,integral_zero] using hx

-- approximate the sum using mist. no bound claiming value at any single perturbed point.
lemma singleNear (f : X → E) (p : Continuous f) (q : HasCompactSupport f) (c : ℝ) (hc : 0 < c) :
    ∃ Y ∈ 𝓝 (0:X), ∀ g, α g ∈ Y → ∀ᶠ i in atTop, dist (S f i) (S (U g ∘ f) i) ≤ c := by
  let Y : Set X := {h : X | (∫ x, ‖f x - f (x+-h)‖) < c}
  refine ⟨Y,(shiftBudget f p q).eventually (gt_mem_nhds hc),fun g v ↦ ?_⟩
  let F' (x : X) := f (x + (-α g))
  have he : HasCompactSupport F' := q.comp_homeomorph (Homeomorph.addRight (-α g))
  filter_upwards [t.shiftActual g f,t.cost (f-F') (p.sub (p.comp
    (continuous_id.add continuous_const))) (q.sub he) c v] with i hx u
  rw [dist_eq_norm,hx, ← t.sum_sub i q he]; exact u.le

def actMist (U : G → E →L[ℂ] E) (f : X → E) (D : Mist G) (x : X) := D.mean fun g ↦ U g (f x)

local notation "D'" a:max f:max => actMist U f a

omit t in
lemma actMist_cont (f : X → E) (p : Continuous f) (D : Mist G) : Continuous (actMist U f D) := by
  induction D with
  | point x => exact (U x).continuous.comp p
  | midP A B h g => exact continuous_const.smul (h.add g)

omit t in
lemma actMist_compact (f : X → E) (p : HasCompactSupport f) (D : Mist G) :
    HasCompactSupport (actMist U f D) := by
  induction D with
  | point x => exact p.comp_left (map_zero (U x))
  | midP A B h g => exact (h.add g).smul_left -- may need explicit r

lemma singleMistNear (f : X → E) (p : Continuous f) (q : HasCompactSupport f) (c : ℝ)
    (hc : 0 < c) (D : ℕ → Mist G) (u : ∀ V ∈ 𝓝 (0:X), ∀ᶠ i in atTop,
      (D i).holds (fun g ↦ α g ∈ V)) :
    ∀ᶠ i in atTop, ∀ᶠ n in atTop, dist (S f n) (S (D' (D i) f) n) ≤ c := by
  obtain ⟨Y,h,H⟩ := t.singleNear f p q c hc
  have ht (M : Mist G) (v : M.holds (fun g ↦ α g ∈ Y)) :
      ∀ᶠ n in atTop, dist (S f n) (S (D' M f) n) ≤ c := by
    induction M with
    | point x => exact H x v
    | midP A B hr hs =>
      filter_upwards [hr (show _ ∧ _ from v).1, hs (show _ ∧ _ from v).2] with i p h
      let a := S (D' A f) i; let b := S (D' B f) i; let x := S f i
      let u := (1/2:ℂ)
      have hz : S (D' (.midP A B) f) i = u • (a+b) := by
        change S (u • (D' A f + D' B f)) i = _
        rw [sum_smul,t.sum_add i (actMist_compact f q A) (actMist_compact f q B)]
      rw [hz,dist_eq_norm]; rw [dist_eq_norm] at p h
      have ha : x - u • (a+b)=u • ((x-a)+(x-b)) := by
        rw [smul_add u (x-a) (x-b),smul_sub,smul_sub,smul_add]
        have hq : u • x + u • x = x := by rw [← add_smul]; unfold u; norm_num
        calc _ = (u • x+u • x) - (u • a+u • b) := congrArg (· - (u • a+u • b)) hq.symm
             _ = _ := by abel
      change ‖x - u • (a+b)‖ ≤ _ ; rw [ha,norm_smul]
      have hx := norm_add_le (x-a) (x-b)
      change ‖x-a‖≤ c at p; change ‖x-b‖≤ c at h
      unfold u; norm_num; linarith
  exact (u Y h).mono fun i v ↦ ht (D i) v

lemma approachProject (project : E →L[ℂ] E) (L : ℝ) (w : ∀ x, ‖project x‖≤ L*‖x‖) (f : X → E)
    (p : Continuous f) (q : HasCompactSupport f) (D : ℕ → Mist G)
    (v : ∀ x, Tendsto (fun i ↦ (D i).mean (fun g ↦ U g x)) atTop (𝓝 (project x))) :
    Tendsto (fun i ↦ ∫ x, ‖(D' (D i) f) x-project (f x)‖) atTop (𝓝 0) := by
  let F i (x : X) := ‖(D' (D i) f) x-project (f x)‖
  have he : Tendsto (fun i ↦ ∫ x, F i x) atTop (𝓝 (∫ _ : X, (0:ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖ + L*‖f x‖)
      (fun i ↦ ((actMist_cont f p _).sub (project.continuous.comp p)).norm.aestronglyMeasurable)
      ?_ ?_ ?_
    · have he := p.norm.integrable_of_hasCompactSupport q.norm (μ:=(volume:Measure X))
      exact he.add (he.const_mul L)
    · intro i; apply ae_of_all; intro x
      rw [Real.norm_of_nonneg (show 0 ≤ F i x from norm_nonneg _)]
      exact (norm_sub_le ..).trans (add_le_add ((D i).mean_budget _ _
        ((D i).solves _ (fun y ↦ (t.norm_eq y (f x)).le))) (w (f x)))
    refine ae_of_all _ fun x ↦ ?_
    have he := ((v (f x)).sub_const (project (f x))).norm; rw [sub_self,norm_zero] at he
    exact he
  simpa using he

-- compare with any eventual value for the projected quadrature (proven by continuous Riemann costs)
lemma projectThen (project : E →L[ℂ] E) (f : X → E)
    (p : Continuous f) (q : HasCompactSupport f) (D : ℕ → Mist G)
    (u : ∀ V ∈ 𝓝 (0:X), ∀ᶠ i in atTop,(D i).holds (fun g ↦ α g ∈ V))
    (v : ∀ x, Tendsto (fun i ↦ (D i).mean (fun g ↦ U g x)) atTop (𝓝 (project x)))
    (z : E) (hp : Tendsto (fun i ↦ S (project ∘ f) i) atTop (𝓝 z)) :
    Tendsto (fun i ↦ S f i) atTop (𝓝 z) := by
  refine Metric.tendsto_nhds.mpr ?_; intro ε hε; let e := ε / 3; have he : 0 < e := by
    unfold e; positivity
  obtain ⟨n,hn,hs⟩ := ((t.singleMistNear f p q e he D u).and
    ((t.approachProject project _ (fun x ↦ project.le_opNorm x) f p q D v).eventually (gt_mem_nhds he))).exists
  have hG := actMist_compact (U:=U) f q (D n)
  have hV : HasCompactSupport (project ∘ f) := q.comp_left (map_zero project)
  have ht := t.cost ((D' (D n) f)-project ∘ f)
    ((actMist_cont f p (D n)).sub (project.continuous.comp p)) (hG.sub hV) e hs
  filter_upwards [hn, ht, Metric.tendsto_nhds.mp hp e he] with i h₁ h₂ h₃
  let w := S (D' (D n) f) i; let y := S (project ∘ f) i
  have hw : dist w y < e := by
    rw [dist_eq_norm]; unfold w y; rw [← t.sum_sub i hG hV]; exact h₂
  exact lt_of_le_of_lt (dist_triangle _ w _) ((add_lt_add_of_le_of_lt h₁
    ((dist_triangle _ y _).trans_lt (add_lt_add hw h₃))).trans_eq (by ring))

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- The unprojected transport sums converge when the projected grid action has a
continuous compactly supported extension *on that vector function*. No dual
separability assumption needed; all estimates strong. -/
theorem limit (project : E →L[ℂ] E) (f : X → E)
    (p : Continuous f) (q : HasCompactSupport f) (D : ℕ → Mist G)
    (u : ∀ V ∈ 𝓝 (0:X), ∀ᶠ i in atTop, (D i).holds (fun g ↦ α g ∈ V))
    (v : ∀ x, Tendsto (fun i ↦ (D i).mean (fun g ↦ U g x)) atTop (𝓝 (project x)))
    (z : X → E) (h : Continuous z) (hc : HasCompactSupport z)
    (hz : ∀ i k, z (place (δ i) k) = U (ρ i k) (project (f (place (δ i) k)))) :
    Tendsto (fun i ↦ S f i) atTop (𝓝 (∫ x, z x)) := by
  refine t.projectThen project f p q D u v _ ((quadrature z h hc t.pos t.vanishes).congr
    (fun i ↦ ?_))
  unfold transportSum; simp_rw [hz]; apply RCLike.real_smul_eq_coe_smul (K:=ℂ)

end Setup
end YM.MacroSix.Grid
#print axioms YM.MacroSix.Grid.Setup.limit
