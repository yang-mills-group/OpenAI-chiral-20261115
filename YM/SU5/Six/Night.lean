import YM.SU5.Six.JointPM
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section

/-! Spectral computations with time increments. Axis 3 as `JointPM`. -/
namespace YM.Six
open MeasureTheory Filter Spectral OS Semigroup Balloon Cheer Boundary Probe
open scoped Topology InnerProductSpace ComplexConjugate NNReal

variable {H : Hilbert} (S : Semigroup H timeAxis)
local notation "Q" => S.ℚmeasure

/-- Axis-3 zero energy. -/
def night : Set E4 := {p | time p = 0}
lemma night_meas : MeasurableSet night := by
  have : Continuous fun p => time p := by fun_prop
  exact (isClosed_eq this continuous_const).measurableSet

lemma fade_night (t : ℝ≥0) {p : E4} (h : p ∈ night) : fade t p = 1 := by
  change p timeAxis = 0 at h
  simp [fade,tinct,h]
lemma conj_fade (t : ℝ≥0) (p : E4) : conj (fade t p) = fade t p := by simp [fade]

lemma morning (t : ℝ≥0) (v : H) : (Q).region night ((1 - S.E t : H.Op) v) = 0 := by
  have hfg := (Q).represents_one.sub (rep_heat S t)
  have hh := hfg.indicator night_meas
  refine norm_eq_zero.mp (sq_eq_zero_iff.mp ?_)
  refine (hh.norm_sq v).trans ?_
  have he (p : E4) : ‖night.indicator (1-fade t) p‖^2 = 0 := by
    by_cases hp : p ∈ night <;> simp [hp,fade_night t]
  simp_rw [he, integral_zero]

/-- The spectral cost in `eq:exactS2`. -/
def tapered (y : Space3) (d t : ℝ≥0) (p : E4) :=
  phasor y p * fade d p * (1-fade t p)^2

lemma tapered_pair (y : Space3) (d t : ℝ≥0) (v w : H) :
    inner ℂ ((1 - S.E t : H.Op) v) (S.U (shore y) (S.E d ((1 - S.E t : H.Op) w))) =
      (Q).pairIntegral (tapered y d t) v w := by
  let A : H.Op := 1 - S.E t
  let T := A.adjoint * (S.U (shore y) * (S.E d * A))
  have hfg := (Q).represents_one.sub (rep_heat S t)
  rw [← ContinuousLinearMap.adjoint_inner_right]
  suffices (Q).Represents (tapered y d t) T from this.on_pair _ _
  have h := hfg.conjugate.mul ((rep_phasor S y).mul ((rep_heat S d).mul hfg))
  convert h using 1
  ext p; dsimp only [tapered,Pi.mul_apply,Pi.sub_apply,Pi.one_apply]
  rw [map_sub,map_one,conj_fade]
  ring
end YM.Six
