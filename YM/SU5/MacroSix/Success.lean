import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Open/dense matrix test from a seed on a box-calendar

Analytic continuation just in each coordinate separately (there using that coordinate's
own positive-*Euclidean*-time evolution). Ordinary topology of ℝ^I. Don't infer joint
rotation or a Wightman prescription. For the matrix work only need product topology /
ordinary entrywise limits.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MacroSix
open Filter Finset Function Set Metric Complex
open scoped Topology NNReal ENNReal BigOperators Pointwise

variable {J : Type*} [Fintype J] [DecidableEq J]

def Success (A : Matrix J J ℂ) : Prop := A.det ≠ 0 ∧ ∀ i, A i i ≠ 0

def compound (A : Matrix J J ℂ) : ℂ := A.det * ∏ i, A i i

lemma success_iff {A : Matrix J J ℂ} : compound A ≠ 0 ↔ Success A := by
  simp only [compound,ne_eq,mul_eq_zero,not_or,Success]; exact and_congr Iff.rfl (Finset.prod_ne_zero_iff.trans (by simp))

lemma compound_limit {T : Type*} (L : Filter T) (A : T → Matrix J J ℂ) (B : Matrix J J ℂ)
    (h : ∀ i j, Tendsto (fun t ↦ A t i j) L (𝓝 (B i j))) :
    Tendsto (compound ∘ A) L (𝓝 (compound B)) := by
  have he : Tendsto (fun x ↦ (A x).det) L (𝓝 B.det) := by
    simp_rw [Matrix.det_apply']
    exact tendsto_finsetSum _ fun u _ ↦ tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ ↦ h (u i) i)
  exact he.mul (tendsto_finsetProd _ fun i _ ↦ h i i)

lemma eventually_success {T : Type*} (L : Filter T) (A : T → Matrix J J ℂ) (B : Matrix J J ℂ)
    (h : ∀ i j, Tendsto (fun t ↦ A t i j) L (𝓝 (B i j))) (p : Success B) :
    ∀ᶠ t in L, Success (A t) :=
  ((compound_limit L A B h).eventually_ne (success_iff.mpr p)).mono fun _ v ↦ success_iff.mp v

lemma compound_analytic (A : ℝ → Matrix J J ℂ) (x : ℝ)
    (h : ∀ i j, AnalyticAt ℝ (fun t ↦ A t i j) x) : AnalyticAt ℝ (compound ∘ A) x := by
  have he : AnalyticAt ℝ (fun t ↦ (A t).det) x := by
    simp_rw [Matrix.det_apply']
    exact Finset.analyticAt_fun_sum _ fun p _ ↦
      analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ ↦ h (p i) i)
  exact he.mul (Finset.analyticAt_fun_prod _ fun i _ ↦ h i i)

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "X" => I → ℝ -- parentheses may need
variable (U : I → Set ℝ)

def rectangle : Set (I → ℝ) := {v | ∀ i, v i ∈ U i}

lemma rectangle_open (h : ∀ i, IsOpen (U i)) : IsOpen (rectangle U) := by
  rw [show rectangle U = ⋂ i, (fun v : I → ℝ ↦ v i) ⁻¹' (U i) from (by ext; simp [rectangle])]
  exact isOpen_iInter_of_finite fun i ↦ (h i).preimage (continuous_apply i)

variable (h : ∀ i, IsOpen (U i)) (t : ∀ i, IsPreconnected (U i))
include h t

lemma on_chamber (K : (X) → Matrix J J ℂ)
    (ha : ∀ i, ∀ v ∈ rectangle U, ∀ j k,
      AnalyticOnNhd ℝ (fun c : ℝ ↦ K (Function.update v i c) j k) (U i))
    (v : X) (hv : v ∈ rectangle U) (hc : Success (K v))
    (P : Set (X)) (p : P⊆rectangle U) (q : P.Nonempty) (r : IsOpen P) :
    ∃ v ∈ P, Success (K v) := by
  have he (x : X) (Hx : x∈rectangle U) (i : I) : AnalyticOnNhd ℝ
      (fun c : ℝ ↦ compound (K (Function.update x i c))) (U i) :=
    fun u w ↦ compound_analytic _ _ fun j k ↦ ha i x Hx j k u w
  by_contra! H
  obtain ⟨a,w⟩ := q
  obtain ⟨ε,e,hε⟩ := Metric.isOpen_iff.mp r _ w
  have hx (b : X) (k : Finset I) (hk : b∈rectangle U) (u : ∀ i, i ∉ k → dist (b i) (a i)<ε) :
      compound (K b)=0 := by
    induction k using Finset.induction_on generalizing b with
    | empty =>
      by_contra he
      exact H b (hε ((dist_pi_lt_iff e).2 fun i ↦ u i (by simp))) (success_iff.mp he)
    | @insert i k v ih =>
      let f (c : ℝ) := Function.update b i c
      have hv : ∀ᶠ x in 𝓝 (a i), compound (K (f x))=0 := by
        filter_upwards [(h i).mem_nhds (show a i∈ U i from (p w : a ∈ rectangle U) i),
          ball_mem_nhds (a i) e] with x r s
        apply ih
        · intro j; by_cases e:j=i
          · subst j; simpa [f]
          rw [show f x j=b j from Function.update_of_ne e ..]; exact hk j
        intro j y; by_cases e : j=i
        · subst j; rw [show f x i=x from Function.update_self ..]; exact s
        exact (by simpa [f,e] using u j (by simp [e,y]))
      have ht : EqOn (fun c : ℝ ↦ compound (K (f c))) (fun _ ↦ 0) (U i) :=
        (he b hk i).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (t i) (p w i) hv
      have ha := ht (hk i)
      simpa [f] using ha
  exact success_iff.mpr hc (hx v Finset.univ hv (by simp))

/-- Pass density to any pairs of independent open pose neighborhoods by varying just the
*second* pose. -/
lemma on_suborder (K : (X) → Matrix J J ℂ)
    (ha : ∀ i, ∀ v ∈ rectangle U, ∀ j k,
      AnalyticOnNhd ℝ (fun c : ℝ ↦ K (Function.update v i c) j k) (U i))
    (v : X) (hv : v∈rectangle U) (hc : Success (K v))
    (A : Set ((X) × (X))) (p : ∀ x∈ A, x.2 - x.1 ∈ rectangle U)
    (q : A.Nonempty) (u : IsOpen A) : ∃ x ∈ A, Success (K (x.2-x.1)) := by
  obtain ⟨x,y⟩ := q
  let W (z : X) := (x.1, z+x.1)
  have he : Continuous W := continuous_const.prodMk (continuous_id.add continuous_const)
  have ht : (W ⁻¹' A).Nonempty := ⟨x.2-x.1,show W _∈ A from (by simp [W,y])⟩
  have hp (z : X) : (W z).2-(W z).1=z := add_sub_cancel_right z _
  obtain ⟨z,b,r⟩ := on_chamber U h t K ha v hv hc _ (fun y hy ↦ hp y ▸ p _ hy) ht (u.preimage he)
  exact ⟨W z,b,by rwa [hp]⟩

lemma denseCost {F : (X) → (X) → Matrix J J ℂ} (K : (X) → Matrix J J ℂ)
    (ha : ∀ i, ∀ v ∈ rectangle U, ∀ j k,
      AnalyticOnNhd ℝ (fun c : ℝ ↦ K (Function.update v i c) j k) (U i))
    (v : X) (hv : v∈rectangle U) (hc : Success (K v)) (A : Set ((X)×(X)))
    (p : ∀ x∈A,x.2-x.1∈rectangle U)
    (e : ∀ x ∈ A, F x.1 x.2 = K (x.2-x.1)) (u : IsOpen A) :
    A ⊆ closure (A ∩ {v | Success (F v.1 v.2)}) := by
  intro i y
  rw [_root_.mem_closure_iff]
  intro D q r
  obtain ⟨x,⟨w,d⟩,H⟩ := on_suborder U h t K ha v hv hc (A∩D)
    (fun i v ↦ p i v.1) ⟨i,y,r⟩ (u.inter q)
  exact ⟨x,d,w,show Success _ from e x w ▸ H⟩
end YM.MacroSix
#print axioms YM.MacroSix.denseCost
