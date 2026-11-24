import YM.Spectral.Projection
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounded spectral multiplier API for `YM.Spectral.PVM` (1)

For spectral pair-integrals we work **by polarization** of the positive
finite measures (`PVM.diagonal`), not by introducing a separate type of
complex measures. Use star in the FIRST variable.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Spectral.PVM
open MeasureTheory Filter Function Set
open scoped Topology InnerProductSpace ComplexConjugate

variable {H : Hilbert} {X : Type*} [MeasurableSpace X]

/-- Borel in the sense of measurable (on a general measurable space), and bounded. -/
structure BB (f : X → ℂ) : Prop where
  me : Measurable f
  bound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

variable {f g f' g' : X → ℂ}

lemma BB.integrable (h : BB f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨c,hc⟩ := h.bound
  exact Integrable.of_bound h.me.aestronglyMeasurable c (ae_of_all _ hc)

lemma BB.pos_bound (h : BB f) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨a,A⟩ := h.bound
  exact ⟨_, zero_lt_one.trans_le (le_max_left 1 a), fun x => le_trans (A x) (le_max_right ..)⟩
lemma BB.const (c : ℂ) : BB (fun _ : X => c) := ⟨measurable_const, _, fun _ => le_refl _⟩
lemma BB.mul (hf : BB f) (hg : BB g) : BB (f*g) := by
  obtain ⟨a,ha,A⟩ := hf.pos_bound; obtain ⟨b,B⟩ := hg.bound
  exact ⟨hf.me.mul hg.me, a*b,fun x => (norm_mul _ _).le.trans
    (mul_le_mul (A x) (B x) (norm_nonneg _) ha.le)⟩
lemma BB.add (hf : BB f) (hg : BB g) : BB (f+g) := by
  obtain ⟨a,A⟩ := hf.bound; obtain ⟨b,B⟩ := hg.bound
  exact ⟨hf.me.add hg.me,a+b,fun x => (norm_add_le _ _).trans (add_le_add (A x) (B x))⟩
lemma BB.conjugate (hf : BB f) : BB (fun x => conj (f x)) := by
  obtain ⟨a,A⟩ := hf.bound
  exact ⟨Complex.continuous_conj.measurable.comp hf.me,a,fun x => by simpa using A x⟩

variable (P : PVM H X)

/-- AE equality for every positive diagonal measure. -/
def Same (f g : X → ℂ) := ∀ x, f =ᵐ[P.diagonal x] g
/-- Has an everywhere-bounded Borel representative. -/
def Admissible (f : X → ℂ) := ∃ g, BB g ∧ P.Same f g

lemma admBB (h : BB f) : P.Admissible f := ⟨f,h,fun _ => .rfl⟩

variable {P}
lemma Admissible.integrable (hf : P.Admissible f) (x : H) : Integrable f (P.diagonal x) := by
  obtain ⟨g,h,t⟩ := hf
  exact (h.integrable (P.diagonal x)).congr (t x).symm

lemma Same.symm (h : P.Same f g) : P.Same g f := fun x => (h x).symm
lemma Same.adm (h : P.Same f g) (a : P.Admissible f) : P.Admissible g := by
  obtain ⟨b,hb,p⟩ := a
  exact ⟨b,hb, fun x => (h x).symm.trans (p x)⟩
lemma Same.mul (hf : P.Same f f') (hg : P.Same g g') : P.Same (f*g) (f'*g') :=
  fun x => (hf x).mul (hg x)
lemma Admissible.mul (hf : P.Admissible f) (hg : P.Admissible g) : P.Admissible (f*g) := by
  obtain ⟨_,u,hu⟩ := hf; obtain ⟨_,v,hv⟩ := hg
  exact ⟨_,u.mul v,hu.mul hv⟩
lemma Admissible.smul (hf : P.Admissible f) (c : ℂ) : P.Admissible (c•f) :=
  (admBB P (BB.const c)).mul hf
lemma Admissible.add (hf : P.Admissible f) (hg : P.Admissible g) : P.Admissible (f+g) := by
  obtain ⟨_,u,hu⟩ := hf; obtain ⟨_,v,hv⟩ := hg
  exact ⟨_, u.add v, fun x => (hu x).add (hv x)⟩
lemma Admissible.conjugate (hf : P.Admissible f) :
    P.Admissible (fun x => conj (f x)) := by
  obtain ⟨_,u,hu⟩ := hf
  exact ⟨_, u.conjugate, fun x => (hu x).fun_comp conj⟩

variable (P)

/-- Polarization, linear-in-second convention. -/
def polarize (q : H → ℂ) (x y : H) : ℂ :=
  (q (x+y) - q (x-y) - Complex.I * (q (x+Complex.I • y) - q (x-Complex.I • y))) / 4

/-- `∫ f dν_{x,y}` as an abbreviation by polarization in terms of
integrals against finite positive Borel (for `X = YM.E4`) measures.
Use for admissible costs. -/
def pairIntegral (f : X → ℂ) : H → H → ℂ := polarize fun v => ∫ p, f p ∂P.diagonal v

lemma polarize_op (T : H.Op) (x y : H) :
    polarize (fun v : H => inner ℂ v (T v)) x y = inner ℂ x (T y) := by
  unfold polarize
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_sub_left, inner_add_right,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf; rw [Complex.I_sq]; ring

/-- `T` is the bounded spectral multiplier of `f`. Use for costs f AE equal
to a bounded Borel function. -/
structure Represents (f : X → ℂ) (T : H.Op) : Prop where
  admissible : P.Admissible f
  on_diag (v : H) : inner ℂ v (T v) = ∫ p, f p ∂P.diagonal v

variable {P} {T U : H.Op}
lemma Represents.on_pair (h : P.Represents f T) (x y : H) :
    inner ℂ x (T y) = P.pairIntegral f x y := by
  rw [←polarize_op, pairIntegral, funext h.on_diag]

lemma Represents.unique (h : P.Represents f T) (k : P.Represents f U) : T = U := by
  ext1 v; exact ext_inner_left ℂ fun x => (h.on_pair x v).trans (k.on_pair x v).symm

lemma Represents.congr (h : P.Represents f T) (he : P.Same f g) : P.Represents g T :=
  ⟨he.adm h.admissible,fun x => (h.on_diag x).trans (integral_congr_ae (he x))⟩
lemma Represents.add (h : P.Represents f T) (k : P.Represents g U) :
    P.Represents (f+g) (T+U) := by
  refine ⟨h.admissible.add k.admissible, fun x => ?_⟩
  rw [add_apply, inner_add_right, h.on_diag, k.on_diag]
  exact (integral_add (h.admissible.integrable x) (k.admissible.integrable x)).symm
lemma Represents.smul (h : P.Represents f T) (c : ℂ) :
    P.Represents (c•f) (c•T) := by
  refine ⟨h.admissible.smul c, fun x => ?_⟩
  rw [smul_apply, inner_smul_right, h.on_diag]
  exact (integral_smul c f).symm
lemma Represents.neg (h : P.Represents f T) : P.Represents (-f) (-T) :=
  neg_one_smul ℂ T ▸ neg_one_smul ℂ f ▸ h.smul (-1)
lemma Represents.sub (h : P.Represents f T) (k : P.Represents g U) :
    P.Represents (f-g) (T-U) := by
  rw [sub_eq_add_neg f g, sub_eq_add_neg T U]; exact h.add k.neg
lemma Represents.conjugate (h : P.Represents f T) :
    P.Represents (fun x => conj (f x)) (T.adjoint) := by
  refine ⟨h.admissible.conjugate, fun v => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, ←inner_conj_symm, h.on_diag, integral_conj]

variable (P)
lemma represents_indicator (s : Set X) (hs : MeasurableSet s) :
    P.Represents (s.indicator fun _ => 1) (P.region s) := by
  refine ⟨admBB _ ⟨measurable_const.indicator hs, 1, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p ∈ s
    · simp [hp]
    simp [hp]
  intro v
  rw [integral_indicator hs, setIntegral_const, ← P.at_pair hs v]
  simp
lemma represents_one : P.Represents (1 : X → ℂ) 1 := by
  have h := represents_indicator P Set.univ .univ
  rwa [P.all, indicator_univ] at h

/-- Set prices of the polarized convention are exactly projection pairings. -/
lemma pairIntegral_indicator (s : Set X) (hs : MeasurableSet s) (x y : H) :
    P.pairIntegral (s.indicator fun _ => 1) x y = inner ℂ x (P.region s y) :=
  ((represents_indicator P s hs).on_pair ..).symm

end YM.Spectral.PVM
