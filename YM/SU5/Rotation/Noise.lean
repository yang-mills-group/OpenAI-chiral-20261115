import YM.RG.Block
import YM.Next.RANK.Axial
import YM.CF.Fixed.Triangular
import YM.CF.Matter.Rep

/-!
# Step (not state) probability, and a uniform noise floor for the plaquette

Formalization for SatinDeterminingRotations, f9574346 §4.
As in the cross-check the earlier construction, freeze all but *one* of the lower links;
we pay a constant uniform even in the volume. All Mark/kernel equalities
and bounds here and in the lift argument are pointwise.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SU5Rotation

open Lattice Wilson RG CF MeasureTheory Function
open scoped Topology BigOperators Matrix.Norms.Frobenius Matrix

section noise
variable {G : Gauge} {c f : Side} (A : StepData c f) (β : ℝ)

/-- Single-link normalized weight in the StepData kernel, given prediction `y`. -/
def linkWeight (y x : G.El) : ℝ :=
  (A.penaltyZ β G)⁻¹ * A.penaltyWeight β (x*y⁻¹)

theorem linkWeight_continuous (y : G.El) : Continuous (linkWeight A β y) :=
  continuous_const.mul ((A.penaltyWeight_cont β).comp (continuous_id.mul continuous_const))

theorem linkWeight_pos (y x : G.El) : 0 < linkWeight A β y x :=
  mul_pos (inv_pos.mpr (A.penaltyZ_pos _)) (Real.exp_pos _)

theorem linkWeight_total (y : G.El) : (∫ x, linkWeight A β y x ∂G.probHaar) = 1 := by
  have h := (measurePreserving_mul_right G.probHaar y⁻¹).integral_comp
    ((Homeomorph.mulRight y⁻¹).measurableEmbedding) (A.penaltyWeight β)
  unfold linkWeight
  rw [integral_const_mul, h, ← StepData.penaltyZ, inv_mul_cancel₀ (A.penaltyZ_pos β).ne']

/-- The floor `exp(-2c')`, `c'=2 B |penalty|`. It will not depend on period
or on cutoff along the chosen step. -/
def noiseFloor (B penalty : ℝ) : ℝ := Real.exp (- (2 * (2 * B * |penalty|)))

theorem noiseFloor_pos (B penalty : ℝ) : 0 < noiseFloor B penalty := Real.exp_pos _

theorem linkWeight_bounds {B : ℝ} (hβ : |β| ≤ B) (y x : G.El) :
    linkWeight A β y x ∈ Set.Icc (noiseFloor B A.kernel.penalty)
      (noiseFloor B A.kernel.penalty)⁻¹ := by
  let R := 2 * B * |A.kernel.penalty|
  have hr (v : G.El) : |-β * A.kernel.penalty * G.price v| ≤ R := by
    have he := G.price_range v
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg he.1]
    refine (mul_le_mul (mul_le_mul_of_nonneg_right hβ (abs_nonneg _)) he.2 he.1
      (mul_nonneg ((abs_nonneg β).trans hβ) (abs_nonneg _))).trans_eq ?_
    dsimp [R]; ring
  have hr' (v : G.El) : A.penaltyWeight β v ∈ Set.Icc (Real.exp (-R)) (Real.exp R) :=
    ⟨Real.exp_le_exp.mpr (abs_le.mp (hr v)).1, Real.exp_le_exp.mpr (abs_le.mp (hr v)).2⟩
  have hi : Integrable (A.penaltyWeight β) G.probHaar :=
    (A.penaltyWeight_cont β).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz₁ : Real.exp (-R) ≤ A.penaltyZ β G := by
    simpa [StepData.penaltyZ] using
      (integral_mono (integrable_const _) hi fun v => (hr' v).1)
  have hz₂ : A.penaltyZ β G ≤ Real.exp R := by
    simpa [StepData.penaltyZ] using
      (integral_mono hi (integrable_const _) fun v => (hr' v).2)
  have hc : noiseFloor B A.kernel.penalty = Real.exp (-R) * Real.exp (-R) := by
    rw [← Real.exp_add]; unfold noiseFloor; dsimp [R]; ring_nf
  rw [hc]
  constructor
  · have hk : Real.exp (-R) ≤ (A.penaltyZ β G)⁻¹ := by
      rw [Real.exp_neg]; exact inv_anti₀ (A.penaltyZ_pos _) hz₂
    exact mul_le_mul hk (hr' (x*y⁻¹)).1 (Real.exp_pos _).le (inv_pos.mpr (A.penaltyZ_pos _)).le
  rw [mul_inv_rev, Real.exp_neg, inv_inv]
  have hk : (A.penaltyZ β G)⁻¹ ≤ Real.exp R := by
    refine (inv_anti₀ (Real.exp_pos _) hz₁).trans_eq ?_
    rw [Real.exp_neg, inv_inv]
  exact mul_le_mul hk (hr' (x*y⁻¹)).2 (Real.exp_pos _).le (Real.exp_pos _).le

private lemma compact_pay {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {φ : X → ℝ} (h : Continuous φ) : Integrable φ μ :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem noise_face_floor {B : ℝ} (hβ : |β| ≤ B) (hc : 1 < c.val)
    (p : Face (Per c)) (Q : Config G c) (F : G.El → ℝ) (hF : Continuous F)
    (hF' : ∀ v, 0 ≤ F v) :
    noiseFloor B A.kernel.penalty * (∫ u, F u ∂G.probHaar) ≤
      ∫ V, F (faceValue V p) * A.noise β Q V ∂prior G c := by
  let e : Edge (Site c) := (p.1,p.2.val.1)
  let s : Finset (Edge (Site c)) := Finset.univ.erase e
  let w (i : Edge (Site c)) := linkWeight A β (Q i)
  let q (V : Config G c) := ∏ i∈s, w i (V i)
  have hn (V : Config G c) : A.noise β Q V = w e (V e) * q V :=
    (Finset.mul_prod_erase Finset.univ (fun i => w i (V i)) (Finset.mem_univ e)).symm
  have hp : e ∈ Next.Rank.Axial.edges p := by simp [e, Next.Rank.Axial.edges]
  have hy (V : Config G c) : 0 ≤ q V :=
    Finset.prod_nonneg fun _ _ => (linkWeight_pos ..).le
  have hw (V : Config G c) (u : G.El) : q (update V e u) = q V := by
    apply Finset.prod_congr rfl
    intro j hj; rw [update_of_ne (Finset.mem_erase.mp hj).1]
  have hq : (∫ V, q V ∂prior G c) = 1 := by
    rw [show (∫ V, q V ∂prior G c) = _ from CF.Fixed.Pivots.integral_pivots G s w]
    exact Finset.prod_eq_one fun i _ => linkWeight_total ..
  have Hq : Continuous q := continuous_finsetProd s fun i _ =>
    (linkWeight_continuous A β (Q i)).comp (continuous_apply _)
  have HF : Continuous (fun V : Config G c => F (faceValue V p)) :=
    hF.comp (continuous_travel _ _)
  calc
    _ = noiseFloor B A.kernel.penalty *
        (∫ V, F (faceValue V p) * q V ∂prior G c) := by
      rw [Next.Rank.Axial.pull_link hc p e hp F hF q Hq hw, hq, mul_one]
    _ = ∫ V : Config G c, noiseFloor B A.kernel.penalty * (F (faceValue V p) * q V)
        ∂prior G c := (integral_const_mul ..).symm
    _ ≤ _ := by
      apply integral_mono (compact_pay (continuous_const.mul (HF.mul Hq)))
        (compact_pay (HF.mul ((A.noise_cont β).comp (continuous_const.prodMk continuous_id))))
      intro V
      change noiseFloor _ _ * (F (faceValue V p) * q V) ≤ F (faceValue V p) * A.noise β Q V
      rw [hn]; exact (Eq.trans_le (by ring : noiseFloor B A.kernel.penalty *
        (F (faceValue V p) * q V) = F (faceValue V p) * (noiseFloor B A.kernel.penalty * q V))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (linkWeight_bounds A β hβ (Q e) (V e)).1 (hy V)) (hF' _)))

/-- Continuous in the *lower* link argument, the upper field frozen. -/
theorem continuous_lower_density (U : Config G f) : Continuous (A.density β U) := by
  let F (t : A.Choices) (V : Config G c) := A.likelihood U t * A.noise β (A.prediction U t) V
  have ht (X : Config G c) : Continuous (fun V => A.noise β X V) := by
    have e := (A.noise_cont (G:=G) β).comp ((continuous_const (y:=X)).prodMk (continuous_id (X:=Config G c)))
    simpa only [Function.comp_def, id_eq] using e
  have h (t : A.Choices) : Continuous (F t) :=
    (continuous_const (y:=A.likelihood U t)).mul (ht (A.prediction U t))
  have H := continuous_finsetSum (f:=F) Finset.univ (fun i _ => h i)
  rw [show A.density β U = (fun V => ∑ t, F t V) from rfl]
  exact H

/-- Scalar kernel average at the upper configuration, not RG.push (the other
integration direction), not a signed reading. -/
def average (U : Config G f) (h : Config G c → ℝ) : ℝ :=
  ∫ V, h V * A.density β U V ∂prior G c

theorem average_face_floor {B : ℝ} (hβ : |β| ≤ B) (hb : A.patch.Branches A.kernel G)
    (hc : 1 < c.val) (p : Face (Per c)) (U : Config G f) (F : G.El → ℝ)
    (hF : Continuous F) (hF' : ∀ v, 0 ≤ F v) :
    noiseFloor B A.kernel.penalty * (∫ u, F u ∂G.probHaar) ≤
      average A β U (fun V => F (faceValue V p)) := by
  let J := noiseFloor B A.kernel.penalty * (∫ u, F u ∂G.probHaar)
  let f₀ (V : Config G c) := F (faceValue V p)
  let v t (V : Config G c) := f₀ V * A.noise β (A.prediction U t) V
  have h (V : Config G c) : f₀ V * A.density β U V = ∑ t, A.likelihood U t * v t V := by
    rw [StepData.density, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; dsimp only [v]; ring
  have HF : Continuous f₀ := hF.comp (continuous_travel _ _)
  change J ≤ ∫ V, f₀ V * A.density β U V ∂prior G c
  simp_rw [h]; rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    calc
      J = ∑ t, A.likelihood U t * J := by rw [← Finset.sum_mul, A.chosen hb, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
        (noise_face_floor A β hβ hc p (A.prediction U t) F hF hF') (A.likelihood_pos U t)
  exact fun t _ => (compact_pay (HF.mul ((A.noise_cont β).comp
    (continuous_const (y:= A.prediction U t) |>.prodMk continuous_id)))).const_mul _

end noise

/-- For Satin Mark `[W]` take the normalized real trace in the defining representation. -/
def traceTest (v : SU.E) := 1 - SU.group.price v

lemma traceTest_mat (v : SU.E) : traceTest v = (SU.fund v).trace.re / 5 := by
  unfold traceTest Gauge.price
  rw [sub_sub_cancel]
  change (SU.fund v).trace.re / ((5 : ℕ):ℝ) = _
  norm_num

lemma traceTest_conj (u v : SU.E) : traceTest (u*v*u⁻¹) = traceTest v := by
  unfold traceTest; rw [Gauge.price_conj]

lemma continuous_traceTest : Continuous traceTest := continuous_const.sub SU.group.continuous_price

private def signs : Fin 5 → ℂ := ![-1,-1,1,1,1]
private def demo : SU.E := by
  let Q := Matrix.diagonal signs
  have h₁ : star Q = Q := by
    unfold Q; rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    apply congrArg Matrix.diagonal
    funext i; fin_cases i <;> simp [signs]
  have h₂ : Q*Q=1 := by
    unfold Q; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i; fin_cases i <;> simp [signs]
  have h₃ : Matrix.det Q=1 := by
    unfold Q; rw [Matrix.det_diagonal]
    norm_num [signs, Fin.prod_univ_succ]
  exact ⟨⟨Q, (by change star Q * Q=1 ∧ Q * star Q=1; rw [h₁]; exact ⟨h₂,h₂⟩)⟩,h₃⟩

lemma traceTest_nonconstant : ∃ x : SU.E, traceTest x ≠ traceTest 1 := by
  refine ⟨demo,?_⟩
  rw [traceTest_mat demo, show SU.fund demo = Matrix.diagonal signs from rfl,
    Matrix.trace_diagonal]
  norm_num [traceTest, signs, Fin.sum_univ_succ]

/-- Haar variance on the loop holonomy. -/
def haarMean := ∫ u, traceTest u ∂SU.group.probHaar
def haarVariance := ∫ u, (traceTest u - haarMean)^2 ∂SU.group.probHaar

theorem haarVariance_pos : 0 < haarVariance := by
  have he : ∃ x, traceTest x ≠ haarMean := by
    obtain ⟨x,hx⟩ := traceTest_nonconstant
    by_cases h : traceTest 1 = haarMean
    · exact ⟨x, h ▸ hx⟩
    exact ⟨1,h⟩
  obtain ⟨x,h⟩ := he
  have hc : Continuous (fun u => (traceTest u - haarMean)^2) :=
    (continuous_traceTest.sub continuous_const).pow 2
  exact integral_pos_of_integrable_nonneg_nonzero hc (compact_pay hc) (fun v => sq_nonneg _)
    (pow_ne_zero 2 (sub_ne_zero.mpr h))

-- Code once for both squares. Completion with an everywhere normalized density.
private theorem expand_center {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ] {h w : X → ℝ}
    (hc : Continuous h) (hw : Continuous w) (hp : (∫ x, w x ∂μ)=1) (m : ℝ) :
    (∫ x, (h x - m)^2 * w x ∂μ) =
      (∫ x, h x^2 * w x ∂μ) - (2*m)*(∫ x, h x * w x ∂μ) + m^2 := by
  have hs x : (h x - m)^2 * w x = h x^2 * w x - (2*m)*(h x*w x)+m^2*w x := by ring
  have hu₁ : Integrable (fun x => h x^2 * w x) μ := compact_pay ((hc.pow 2).mul hw)
  have hu₂ := (show Integrable (fun x => h x * w x) μ from compact_pay (hc.mul hw)).const_mul (2*m)
  simp_rw [hs]
  rw [integral_add (show Integrable (fun x => h x^2*w x - (2*m)*(h x*w x)) μ from
    hu₁.sub hu₂) ((compact_pay hw).const_mul (m^2)), integral_sub hu₁ hu₂,
    integral_const_mul, integral_const_mul, hp, mul_one]

theorem variance_le_centered (m : ℝ) :
    haarVariance ≤ ∫ x, (traceTest x - m)^2 ∂SU.group.probHaar := by
  have h (r : ℝ) : (∫ x, (traceTest x - r)^2 ∂SU.group.probHaar) =
      (∫ x, traceTest x^2 ∂SU.group.probHaar) - (2*r)*haarMean + r^2 := by
    simpa [haarMean] using expand_center (μ:=SU.group.probHaar) continuous_traceTest
      (continuous_const (y:=(1:ℝ))) (by simp) r
  rw [haarVariance, h, h]
  nlinarith [sq_nonneg (m - haarMean)]

/-- The actual `faceValue` of the four-link plaquette is Haar in unbiased link-prior
integration, in every such (nondegenerate) torus. -/
theorem haar_face {G : Gauge} {c : Side} (hc : 1 < c.val) (p : Face (Per c))
    (F : G.El → ℝ) (hF : Continuous F) :
    (∫ V : Config G c, F (faceValue V p) ∂prior G c) = ∫ x, F x ∂G.probHaar := by
  simpa using Next.Rank.Axial.pull_link hc p (p.1,p.2.val.1)
    (by simp [Next.Rank.Axial.edges]) F hF _ (continuous_const (y:=(1:ℝ))) (by intros; rfl)

/-- A trace test on an actual lower torus. -/
def torusTrace {c : Side} (p : Face (Per c)) (V : Config SU.group c) := traceTest (faceValue V p)

lemma continuous_torusTrace {c : Side} (p : Face (Per c)) : Continuous (torusTrace p) :=
  continuous_traceTest.comp (continuous_travel _ _)

/-- Uniform-in-volume conditional variance cutoff estimate for this stencil. Strictly
positive RHS of the estimate written `A(W²)-A(W)² ≥ positive`; no almost-everywhere
qualifier. This is not the signed Schwinger law. -/
theorem cutoff_variance {c f : Side} (A : StepData c f) (β B : ℝ) (hβ : |β| ≤ B)
    (hb : A.patch.Branches A.kernel SU.group) (hc : 1 < c.val)
    (p : Face (Per c)) (U : Config SU.group f) :
    noiseFloor B A.kernel.penalty * haarVariance ≤
      average A β U (fun x => torusTrace p x ^ 2) - average A β U (torusTrace p)^2 := by
  let m := average A β U (torusTrace p)
  have he := expand_center (μ:=prior SU.group c) (continuous_torusTrace p)
    (continuous_lower_density A β U) (A.density_total hb β U) m
  change average A β U (fun x => (torusTrace p x - m)^2) =
    average A β U (fun x => torusTrace p x ^ 2) - 2*m*m + m^2 at he
  change _ ≤ _ - m^2
  calc
    _ ≤ noiseFloor B A.kernel.penalty * ∫ x, (traceTest x - m)^2 ∂SU.group.probHaar :=
      mul_le_mul_of_nonneg_left (variance_le_centered m) (noiseFloor_pos ..).le
    _ ≤ average A β U (fun x => (torusTrace p x - m)^2) :=
      average_face_floor A β hβ hb hc p U _
        ((continuous_traceTest.sub continuous_const).pow 2) (fun v => sq_nonneg _)
    _ = _ := he.trans (by ring)

lemma varianceBound_pos (B p : ℝ) : 0 < noiseFloor B p * haarVariance :=
  mul_pos (noiseFloor_pos ..) haarVariance_pos

end YM.SU5Rotation

#print axioms YM.SU5Rotation.linkWeight_bounds
#print axioms YM.SU5Rotation.haar_face
#print axioms YM.SU5Rotation.cutoff_variance
#print axioms YM.SU5Rotation.varianceBound_pos
