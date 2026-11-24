/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import Mathlib.Analysis.Calculus.Deriv.Prod
import YM.CF.Fock.Ratio
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Complex log bill without branch choice for arbitrary volumes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology
open Set Function MeasureTheory
attribute [local instance] opCStarAlgebra
variable {n : Type*} [DecidableEq n] [Fintype n]
-- complex derivative variant of YM.AnalyticNext.ConnectedActivity.ResolventVolume.hasDerivAt_det
lemma det_der {f : ℂ → Op n} {B : Op n} {t : ℂ} (h : IsUnit (f t)) (g : ∀ i j, HasDerivAt (fun x => f x i j) (B i j) t) :
    HasDerivAt (fun x => (f x).det) (((f t)⁻¹ * B).trace * (f t).det) t := by
  let V := f t
  let D : ContinuousMultilinearMap ℂ (fun _ : n => n → ℂ) ℂ :=
    { Matrix.detRowAlternating.toMultilinearMap with
      cont := by
        change Continuous fun A : n → n → ℂ => (Matrix.of A).det
        refine (continuous_matrix ?_).matrix_det
        intro i j; simp only [Matrix.of_apply]; fun_prop }
  have he : HasDerivAt (fun x (i j : n) => f x i j) (fun i j => B i j) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => g i j
  let G := B * V⁻¹
  have hh : G * V = B := by unfold G V; rw [mul_assoc,(live h).2,mul_one]
  have hu (i : n) : Matrix.det (V.updateRow i (B i)) = G i i * V.det := by
    have H : (∑ k, G i k • V k) = B i := by
      funext m; nth_rewrite 1 [Finset.sum_apply]; exact congr_fun (congr_fun hh i) m
    rw [← H]; exact Matrix.det_updateRow_sum ..
  have hx := (D.hasFDerivAt _).comp_hasDerivAt t he
  rw [ContinuousMultilinearMap.linearDeriv_apply] at hx
  rw [Matrix.trace_mul_comm, Matrix.trace, Finset.sum_mul]
  change HasDerivAt (fun x => (f x).det) (∑ i, G i i * V.det) t
  change HasDerivAt (fun x => (f x).det) (∑ i, Matrix.det (V.updateRow i (B i))) t at hx
  simpa only [hu] using hx

-- straight segment 1→1+A
def beam (A : Op n) (x : ℂ) : Op n := 1+x • A
def slope (A : Op n) (x : ℝ) : ℂ := ((beam A x)⁻¹*A).trace
def invoice (A : Op n) : ℂ := ∫ x in (0:ℝ)..1, slope A x
lemma beam_active {A : Op n} (h : ‖A‖ < 1) (x : ℝ) (g : x∈uIcc (0:ℝ) 1) : IsUnit (beam A x) := by
  rw [uIcc_of_le zero_le_one] at g; apply nearOne
  unfold beam; rw [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg,norm_smul,Complex.norm_real,Real.norm_of_nonneg g.1]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right g.2 (norm_nonneg _)) (by rw [one_mul]; exact h)
lemma slope_j {A : Op n} {x : ℝ} (h : IsUnit (beam A x)) : ContinuousAt (fun p : Op n × ℝ => slope p.1 p.2) (A,x) := by
  let f := fun p : Op n × ℝ => beam p.1 p.2
  have hf : Continuous f := by unfold f beam; fun_prop
  have H : ContinuousAt (fun p : Op n × ℝ=> (f p)⁻¹) (A,x) := by
    change ContinuousAt ((fun X:Op n=>X⁻¹) ∘ f) _
    exact (InvC_cont (A:=f (A,x)) h).comp hf.continuousAt
  have ht := (H.mul (continuous_fst (X:=Op n) (Y:=ℝ)).continuousAt)
  change ContinuousAt ((fun A : Op n=>A.trace) ∘ _) _; exact ((continuous_id.matrix_trace).continuousAt).comp ht
lemma slope_at {A : Op n} {x : ℝ} (h : IsUnit (beam A x)) : ContinuousAt (slope A) x :=
  (slope_j h).comp (f:=fun t=>(A,t)) (continuousAt_const.prodMk continuousAt_id)
lemma slope_meas (A : Op n) : StronglyMeasurable (slope A) := by
  -- use matrix adjugate explicit, finite-dimensional Borel
  letI : MeasurableSpace (Op n) := borel _
  haveI : BorelSpace (Op n) := ⟨rfl⟩
  let f := fun t:ℝ=>beam A t
  have he : Continuous f := by unfold f beam; fun_prop
  have hi : Measurable (fun t=>(f t)⁻¹) := by
    simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]
    exact (he.matrix_det.measurable.inv).smul (he.matrix_adjugate.measurable)
  exact (((show Continuous fun x:Op n=>x.trace from continuous_id.matrix_trace).measurable).comp (hi.mul (show Measurable (fun _ : ℝ => A) from measurable_const))).stronglyMeasurable
lemma factor (A : Op n) (h : ‖A‖ < 1) : Complex.exp (invoice A)=(1+A).det := by
  let L := uIcc (0:ℝ) 1; let f := fun t : ℝ => ∫ x in (0:ℝ)..t, slope A x
  let D := fun x : ℝ => (beam A x).det * Complex.exp (-f x)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=D) (f':=fun _ => 0) (a:=0) (b:=1)
  have hD (x) (hx:x∈L) : HasDerivAt D 0 x := by
    have Ht : ContinuousOn (slope A) L := fun t ht => (slope_at (beam_active h t ht)).continuousWithinAt
    have hi := beam_active h x hx
    have hf : HasDerivAt f (slope A x) x := intervalIntegral.integral_hasDerivAt_right (Ht.mono (by
      exact uIcc_subset_uIcc_left hx -- tune
      ) |>.intervalIntegrable) ((slope_meas A).stronglyMeasurableAtFilter) (slope_at hi)
    have Hg i j : HasDerivAt (fun t=>beam A t i j) (A i j) (x:ℂ) := by simpa [beam] using (((hasDerivAt_id' (x:ℂ)).mul_const (A i j)).const_add ((1:Op n) i j))
    have ht := (det_der hi Hg).comp_ofReal.mul (hf.neg.cexp)
    convert! ht using 1
    unfold slope; ring
  have ht := he hD (by simp); simp only [D,f,intervalIntegral.integral_same,inv_one,Complex.exp_zero,mul_one,
    Complex.exp_neg,Complex.ofReal_zero,Complex.ofReal_one,beam,one_smul,zero_smul,add_zero,
    Matrix.det_one,intervalIntegral.integral_zero] at ht
  change 0=Matrix.det (1+A)*(Complex.exp (invoice A))⁻¹-1 at ht
  have h₁ := sub_eq_zero.mp ht.symm; field_simp at h₁; exact h₁.symm
end YM.CF.Fock
