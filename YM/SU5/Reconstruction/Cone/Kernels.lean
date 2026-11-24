import YM.Heat.Lift
import YM.OS.Core
import YM.Mink.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-!
# Cone pressure: one Euclidean two-stamp reflection budget

In any physical orientation with OS.semigroup, no rotation hypothesis needed.
Here formula in terms of quantities that can be evaluated on EUCLIDEAN data.
Time energy positivity is already present; testing transverse surf as small as
specified suffices for full cone. Uses genuine PVM, no assuming density of point
fields or continuity of U in Op norm.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.ConePrice
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup Boundary Probe
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x

@[simp] lemma sep_along (a : Axis) (x : Cross a) : SEP a x.val=x := Subtype.ext (show _ = x.val from by
  change x.val-x.val a • basis a=_; rw [show x.val a=0 from x.property,zero_smul,sub_zero])
lemma sep_size {a : Axis} (x : E4) : ‖SEP a x‖^2 = ‖x‖^2-(x a)^2 := by
  change ‖x-x a • basis a‖^2=_
  rw [norm_sub_sq (𝕜:=ℝ),norm_smul, real_inner_smul_right, real_inner_comm (basis a), basis_inner]
  simp [Real.norm_eq_abs,sq_abs] -- tune
  ring
@[simp] lemma translation (x : Cross a) : S.unit.translation x.val=S.U x := by
  unfold unit; simp only [show x.val a=0 from x.property, sep_along, S.birth, ContinuousLinearMap.id_comp]

/-- same convention as `Mink.cone`. -/
def front (a : Axis) := {x:E4 | ‖SEP a x‖ ≤ x a}
lemma canonical : front timeAxis = Mink.cone := by
  ext x; change ‖_‖≤_ ↔ ‖_‖≤_
  rw [show ‖SEP timeAxis x‖=‖spatial x‖ from (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [sep_size,Mink.squares]; exact add_sub_cancel_right ..)]
  rfl
lemma closed_front (a : Axis) : IsClosed (front a):=isClosed_le (by fun_prop) (by fun_prop)

/-- Cone momentum spectrum of the physical (`U,E`-reconstructed) motion. -/
abbrev Forward : Prop := S.ℚmeasure.region (front a)ᶜ=0

section damped
variable (x : H) (t : ℝ≥0) (y : OS.Cross a)
local notation "v" => (‖x‖*‖x‖)
local notation "T" => ((t:ℝ):ℂ)
local notation "I" => Complex.I
-- weight of palette cell for spatial-angle/time-only displacement
noncomputable def amplitude (y : OS.Cross a) (t : ℝ≥0) (p : E4) := Real.cos (inner ℝ p y.val) * Real.exp (-(p a)*(t:ℝ))
local notation "Jp" p:max => Complex.exp ((p a:ℂ)*(T*I)*I)
private lemma amp (p : E4) : (plane p y.val * Jp p).re = amplitude y t p := by
  unfold amplitude plane; rw [← Complex.exp_add,Complex.exp_re]; simp; ring

lemma comp_can : Integrable (fun p : E4 => plane p y.val * Jp p) (𝔪 x) :=
  Paley.ok (𝔪 x) (fun p=> p a) (by fun_prop) (S.bright x) (fun p=>plane p y.val) (by unfold plane; fun_prop) (fun p=> plane_norm ..) _ (show 0 ≤ (T*I).im from (by simp))
lemma amp_can : Integrable (amplitude y t) (𝔪 x) := by
  have h : ∀ p, RCLike.re (plane p y.val * Jp p) = amplitude y t p := amp t y
  have hm := (comp_can S x t y).re
  simpa only [h] using hm

lemma damped : inner ℂ x (S.U y (S.E t x))= ∫ p, plane p y.val * Jp p ∂𝔪 x := by
  have h := heat S y.val x (z:=T*I) (show 0 ≤ (T*I).im from (by simp))
  unfold J ray at h
  rw [translation,show (T*I).im=(t:ℝ) from by simp, Real.toNNReal_coe,show (T*I).re=0 from by simp,S.birth] at h
  exact h
lemma warm : (inner ℂ x (S.U y (S.E t x))).re = ∫ p, amplitude y t p ∂𝔪 x := by
  rw [damped]; simp_rw [← amp]
  exact (integral_re (comp_can S x t y)).symm

@[simp] lemma amp_time (p : E4) : amplitude (0:Cross a) t p= Real.exp (-(p a)*t) := by simp [amplitude]

lemma warp : (inner ℂ x (S.E t x)).re = ∫ p, amplitude (a:=a) 0 t p ∂𝔪 x := by
  rw [← warm, S.uZero]; rfl
lemma all_norm : (𝔪 x).real univ = ‖x‖^2 := by rw [(P).same .univ,(P).all]; rfl
lemma heat_norm : ‖S.E t x‖^2 = ∫ p, amplitude (a:=a) 0 (t+t) p ∂𝔪 x := by
  rw [← warp,← inner_self_eq_norm_sq (𝕜:=ℂ),S.swing, S.time t t]; rfl
lemma cross_heat : (inner ℂ (S.E t x) (S.U y (S.E t x))).re = ∫ p, amplitude y (t+t) p ∂𝔪 x := by
  rw [S.swing,← ContinuousLinearMap.comp_apply (S.E t) (S.U y), S.independent,← warm,S.time]; rfl
end damped

/-- Signed pressure weight. Combines two squares measured by EU reflection budget. -/
def tension (y : Cross a) (t : ℝ≥0) (p : E4) := 2*(amplitude (a:=a) 0 (t+t) p-amplitude y (t+t) p)-(1-2*amplitude (a:=a) 0 t p+amplitude (a:=a) 0 (t+t) p)

lemma can_enter (x : H) (y : Cross a) (t : ℝ≥0) : Integrable (tension y t) (𝔪 x) := by
  let h := (amp_can S x (t+t) 0)
  exact ((h.sub (amp_can S x _ y)).const_mul (2:ℝ)).sub (((integrable_const _).sub ((amp_can S x t 0).const_mul (2:ℝ))).add h)

/-- Exactly in Hilbert reflection pressure; thus a shot at every state means against every PVM vector. -/
theorem pressure_amount (x : H) (y : Cross a) (t : ℝ≥0) : ‖S.U y (S.E t x)-S.E t x‖^2- ‖x-S.E t x‖^2 = ∫ p, tension y t p ∂𝔪 x := by
  have h₁ := (amp_can S x (t+t) 0); have h₂ := (amp_can S x t 0); have h₃:= amp_can S x (t+t) y
  rw [norm_sub_rev (S.U _ _),norm_sub_sq (𝕜:=ℂ),norm_sub_sq (𝕜:=ℂ),S.unitary]; change ‖_‖^2-2*(inner ℂ _ _).re+_ - (‖x‖^2-2*(inner ℂ _ _).re+_) = _
  have ha : Integrable (fun p:E4=> amplitude (a:=a) 0 (t+t) p - amplitude y (t+t) p) (𝔪 x) := h₁.sub h₃
  have b : Integrable (fun p:E4=>1-2*amplitude (a:=a) 0 t p) (𝔪 x) := (integrable_const _).sub (h₂.const_mul _)
  have c : Integrable (fun p : E4=>1-2*amplitude (a:=a) 0 t p+amplitude (a:=a) 0 (t+t) p) (𝔪 x) := b.add h₁
  unfold tension
  rw [integral_sub (ha.const_mul 2) c, integral_add b h₁, integral_const_mul,integral_sub h₁ h₃,
    integral_sub (integrable_const _) (h₂.const_mul _),integral_const,integral_const_mul,smul_eq_mul, mul_one, heat_norm,cross_heat,warp,← all_norm]
  ring

@[fun_prop] theorem tension_cont (x : Cross a) (t : ℝ≥0): Continuous (tension x t) := by unfold tension amplitude; fun_prop
end YM.ConePrice
