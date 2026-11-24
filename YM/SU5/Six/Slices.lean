import YM.Heat.Extend
import YM.Space.Configurations
set_option autoImplicit false
noncomputable section
namespace YM.Six
open MeasureTheory Filter Metric OS OS.Semigroup Set
open scoped Topology InnerProductSpace ComplexConjugate NNReal ComplexOrder

/-- Real heat pairings are analytic on strictly positive delays. -/
lemma analyticAt_heat {H : Hilbert} {a : Axis} (S : OS.Semigroup H a) (v w : H)
    (t : ℝ) (ht : 0 < t) : AnalyticAt ℝ (fun d : ℝ => inner ℂ v (S.E d.toNNReal w)) t := by
  let f (z : ℂ) := inner ℂ v (S.F z w)
  have h : AnalyticAt ℂ f t :=
    ((innerSL ℂ v).analyticAt _).comp <|
      ((ContinuousLinearMap.apply ℂ H.space w).analyticAt _).comp <|
        S.localHeat t (show 0 < (t:ℂ).re from ht)
  refine ((AnalyticAt.restrictScalars (𝕜:=ℝ) h).comp (Complex.ofRealCLM.analyticAt t)).congr ?_
  filter_upwards [lt_mem_nhds ht] with x hx
  change inner ℂ v (S.F x w) = _
  rw [show (x:ℂ) = duration x.toNNReal from congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal x hx.le).symm,
    S.roots_heat (Real.toNNReal_pos.mpr hx)]

variable {α : Type*} [Fintype α] [DecidableEq α]
/-- Full rank and nonvanishing on every diagonal. -/
def Clean (A : Matrix α α ℂ) := A.det ≠ 0 ∧ ∀ i, A i i ≠ 0
/-- Polynomial for the combined success test. -/
def signal (A : Matrix α α ℂ) := A.det * ∏ i, A i i

lemma clean_iff (A : Matrix α α ℂ) : Clean A ↔ signal A ≠ 0 := by
  simp [Clean, signal, Finset.prod_ne_zero_iff]
lemma continuous_signal : Continuous (signal : Matrix α α ℂ → ℂ) :=
  continuous_id.matrix_det.mul <| continuous_finsetProd _ fun i _ =>
    (continuous_apply i).comp (continuous_apply i)
lemma analyticAt_signal (f : ℝ → Matrix α α ℂ) (t : ℝ)
    (h : ∀ i j, AnalyticAt ℝ (fun x => f x i j) t) : AnalyticAt ℝ (signal ∘ f) t := by
  refine AnalyticAt.mul ?_ (Finset.univ.analyticAt_fun_prod (fun i _ => h i i))
  change AnalyticAt ℝ (fun x => Matrix.det (f x)) t
  simp_rw [Matrix.det_apply, Units.smul_def,zsmul_eq_mul]
  refine Finset.univ.analyticAt_fun_sum (fun σ _ => ?_)
  exact analyticAt_const.mul (Finset.univ.analyticAt_fun_prod (fun i _ => h (σ i) i))

open Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shelf (I : ι → Set ℝ) := {x : ι → ℝ | ∀ i, x i ∈ I i}
omit [Fintype ι] in
lemma shelf_update {I : ι → Set ℝ} {x : ι → ℝ} (hx : x ∈ shelf I) {i : ι} {y : ℝ} (h : y ∈ I i) :
    update x i y ∈ shelf I := by
  intro j; by_cases e : j = i
  · subst j; rwa [update_self]
  rw [update_of_ne e]; exact hx j

/-- Slice analyticity suffices. -/
lemma shelf_dense (f : (ι → ℝ) → ℂ) (I : ι → Set ℝ) (h : ∀ i, IsOpen (I i))
    (c : ∀ i, IsPreconnected (I i))
    (a : ∀ x ∈ shelf I, ∀ i, AnalyticOnNhd ℝ (fun t => f (update x i t)) (I i))
    (v : ∃ x ∈ shelf I, f x ≠ 0) : shelf I ⊆ closure {x ∈ shelf I | f x ≠ 0} := by
  intro x hx; apply Metric.mem_closure_iff.mpr; intro ε he
  by_contra! b
  have g (s : Finset ι) (p : ι → ℝ) (hp : p ∈ shelf I) (w : ∀ j∉s, |x j - p j| < ε) : f p = 0 := by
    induction s using Finset.induction_on generalizing p with
    | empty =>
      by_contra u
      have hg := b p (show p∈_ from ⟨hp,u⟩)
      rw [dist_eq_norm] at hg
      exact (not_lt_of_ge hg) ((pi_norm_lt_iff he).mpr fun i => w i (by simp))
    | @insert i s hi ih =>
      have zero : (fun t => f (update p i t)) =ᶠ[𝓝 (x i)] 0 := by
        filter_upwards [(h i).mem_nhds (hx i), Metric.ball_mem_nhds (x i) he] with t u e
        apply ih _ (shelf_update hp u); intro j z
        by_cases d : j=i
        · subst j; rw [update_self, abs_sub_comm]; exact e
        rw [update_of_ne d]; exact w j (mt Finset.mem_insert.mp fun v=> v.elim d z)
      have t := (a p hp i).eqOn_zero_of_preconnected_of_eventuallyEq_zero (c i) (hx i) zero
      simpa using (t (hp i))
  obtain ⟨p,hp,y⟩ := v; exact y <| g Finset.univ p hp (by simp)

lemma shelf_clean_dense (f : (ι → ℝ) → Matrix α α ℂ) (I : ι → Set ℝ) (h : ∀ i, IsOpen (I i))
    (c : ∀ i, IsPreconnected (I i))
    (a : ∀ x ∈ shelf I, ∀ i j k, AnalyticOnNhd ℝ (fun t => f (update x i t) j k) (I i))
    (v : ∃ x ∈ shelf I, Clean (f x)) : shelf I ⊆ closure {x ∈ shelf I | Clean (f x)} := by
  simp_rw [clean_iff] at v ⊢
  refine shelf_dense (signal ∘ f) I h c ?_ v
  exact fun x hx i t ht=>analyticAt_signal _ _ fun j k=>a x hx i j k t ht


section
variable {X : Type*} [TopologicalSpace X]

lemma clean_open {f : X → Matrix α α ℂ} (hf : Continuous f) : IsOpen {x | Clean (f x)} := by
  simp_rw [clean_iff]; exact isOpen_ne_fun (continuous_signal.comp hf) continuous_const

variable [AddCommGroup X] [IsTopologicalAddGroup X]

lemma diff_dense (S : Set X) {U : Set (X×X)} (h : IsOpen U)
    (he : ∀ x∈U, x.2 - x.1 ∈ closure S) :
    U ⊆ closure {x ∈ U | x.2 - x.1 ∈ S} := by
  intro x hx; apply _root_.mem_closure_iff.mpr; intro o ho x'
  let f (t : X) := (x.1,t+x.1)
  have hf : Continuous f := by unfold f; fun_prop
  have t : x.2-x.1 ∈ f ⁻¹' (o ∩ U) := by simp [f,x',hx]
  obtain ⟨y,⟨a,b⟩,c⟩ := (_root_.mem_closure_iff.mp (he x hx)) _
    ((ho.inter h).preimage hf) t
  exact ⟨f y,a,b,by simpa [f] using c⟩
end
end YM.Six
