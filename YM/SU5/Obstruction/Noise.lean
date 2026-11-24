/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.RG.Block
import YM.CF.Matter.Mass

/-!
# Conditional variation of a plaquette

The law here is the one-step kernel (`StepData.density`), on the actual
SU(5) links, *not* a positivity hypothesis on selected readings. Most of
the minorization proof works on any matrix Gauge. We give a one-link bound
(as in the second version of the gap argument): condition on the physical
tags, preserve the other factors with their full mass, use the lower bound
only on **one** of the lower links. To implement the Fubini argument, move
just this variable through its whole range by Haar translation.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.CF.SatinRotation

open MeasureTheory Function Lattice Wilson RG
open scoped Topology BigOperators Matrix.Norms.Frobenius

section Bound

variable {c f : Side} {G : Gauge} (S : StepData c f)

/-- A per-link bound that can be used uniformly in volumes. -/
def noiseFloor (B penalty : ℝ) := Real.exp (-(2 * (B * penalty * 2)))

theorem noiseFloor_pos (B penalty : ℝ) : 0 < noiseFloor B penalty := Real.exp_pos _

lemma link_weight_ge {β B : ℝ} (h : |β| ≤ B) (u : G.El) :
    noiseFloor B S.kernel.penalty ≤ (S.penaltyZ β G)⁻¹ * S.penaltyWeight β u := by
  let w := B * S.kernel.penalty * 2
  have hw (v : G.El) : Real.exp (-w) ≤ S.penaltyWeight β v ∧
      S.penaltyWeight β v ≤ Real.exp w := by
    have hp := S.kernel.penalty_pos
    have hi := G.price_range v
    have he : |-β * S.kernel.penalty * G.price v| ≤ w := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos hp, abs_of_nonneg hi.1]
      dsimp [w]
      exact mul_le_mul (mul_le_mul_of_nonneg_right h hp.le) hi.2 hi.1
        (mul_nonneg ((abs_nonneg _).trans h) hp.le)
    exact ⟨Real.exp_le_exp.mpr (abs_le.mp he).1, Real.exp_le_exp.mpr (abs_le.mp he).2⟩
  have hz : 0 < S.penaltyZ β G := S.penaltyZ_pos β
  have hZ : S.penaltyZ β G ≤ Real.exp w := by
    have := integral_mono (μ:=G.probHaar)
      ((S.penaltyWeight_cont β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const (Real.exp w)) (fun v => (hw v).2)
    simpa [StepData.penaltyZ] using this
  change Real.exp (-(2*w)) ≤ _
  rw [show -(2*w) = -w + -w by ring, Real.exp_add]
  refine mul_le_mul ?_ (hw u).1 (Real.exp_pos _).le (inv_pos.mpr hz).le
  rw [Real.exp_neg]; exact inv_anti₀ hz hZ

end Bound

section MoveLink
variable {c : Side} {G : Gauge} (e : Edge (Site c))

private lemma prior_mul_preserving (X : Config G c) :
    MeasurePreserving (fun V : Config G c => X * V) (prior G c) (prior G c) :=
  measurePreserving_pi (fun _ => G.probHaar) (fun _ => G.probHaar)
    (fun j : Edge (Site c) => measurePreserving_mul_left G.probHaar (X j))

private lemma link_motion_cont : Continuous fun p : Config G c × G.El => Pi.mulSingle e p.2 * p.1 := by
  apply continuous_pi
  intro j
  simp only [Pi.mul_apply]
  by_cases h : j = e
  · subst j
    simp_rw [Pi.mulSingle_eq_same]
    exact continuous_snd.mul ((continuous_apply _).comp continuous_fst)
  simp_rw [Pi.mulSingle_eq_of_ne h, one_mul]
  exact (continuous_apply _).comp continuous_fst

private lemma move_integrable {h : Config G c → ℝ} (hh : Continuous h) :
    Integrable (fun p : Config G c × G.El => h (Pi.mulSingle e p.2 * p.1))
      ((prior G c).prod G.probHaar) :=
  (hh.comp (link_motion_cont e)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Insert a one-link Haar integral. -/
private lemma move_integral {h : Config G c → ℝ} (hh : Continuous h) :
    (∫ V : Config G c, (∫ u : G.El, h (Pi.mulSingle e u * V) ∂G.probHaar) ∂prior G c) =
      ∫ V, h V ∂prior G c := by
  have hi (u : G.El) :
      (∫ V : Config G c, h (Pi.mulSingle e u * V) ∂prior G c) = ∫ V, h V ∂prior G c :=
    (prior_mul_preserving (Pi.mulSingle e u : Config G c)).integral_comp
      ((Homeomorph.mulLeft (Pi.mulSingle e u : Config G c)).measurableEmbedding) h
  rw [integral_integral_swap]
  · simp_rw [hi]; simp
  exact move_integrable e hh

private lemma move_mono (a : ℝ) {w t : Config G c → ℝ} (hw : Continuous w) (ht : Continuous t)
    (h : ∀ V : Config G c,
      a * (∫ u : G.El, w (Pi.mulSingle e u * V) ∂G.probHaar) ≤
        ∫ u : G.El, t (Pi.mulSingle e u * V) ∂G.probHaar) :
    a * (∫ V, w V ∂prior G c) ≤ ∫ V, t V ∂prior G c := by
  rw [← move_integral e hw, ← move_integral e ht, ← integral_const_mul]
  exact integral_mono ((move_integrable e hw).integral_prod_left.const_mul a)
    (move_integrable e ht).integral_prod_left h

end MoveLink

section Plaquette
variable {c f : Side} {G : Gauge} (S : StepData c f) {β B : ℝ}
variable (p : Face (Per c))

/-- Use the first link of the specified face. -/
private abbrev firstLink : Edge (Site c) := (p.1, p.2.val.1)

/-- Only need that this particular link is read once. -/
private lemma face_move_aux {R E : Type*} [AddCommGroup R] [One R]
    [Group E] [DecidableEq (Edge (Four R))]
    (p : Face R) (hp : p.1 + step p.2.val.2 ≠ p.1)
    (u : E) (V : Links R E) :
    faceValue (Pi.mulSingle (p.1,p.2.val.1) u * V) p = u * faceValue V p := by
  rcases p with ⟨x,⟨⟨i,j⟩,hj⟩⟩
  have hn : j ≠ i := Ne.symm (ne_of_lt (show i < j from hj))
  have hk : x + step j ≠ x := hp
  have h (U : Links R E) : travel U x (square i j) = U (x,i) * U (x+step i,j) *
      (U (x+step j,i))⁻¹ * (U (x,j))⁻¹ := by
    simp [square,travel,sub_eq_add_neg,add_comm,add_assoc,add_left_comm,mul_assoc]
  change travel (Pi.mulSingle (x,i) u * V) x (square i j) = u * travel V x (square i j)
  simp_rw [h]
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (show (x+step i,j) ≠ (x,i) from fun H => hn (congrArg Prod.snd H)),
    Pi.mulSingle_eq_of_ne (show (x,j) ≠ (x,i) from fun H => hn (congrArg Prod.snd H)),
    Pi.mulSingle_eq_of_ne (show (x+step j,i) ≠ (x,i) from fun H => hk (congrArg Prod.fst H)),
    one_mul, mul_assoc]

private lemma face_move (hp : p.1 + step p.2.val.2 ≠ p.1)
    (u : G.El) (V : Config G c) :
    faceValue (Pi.mulSingle (firstLink p) u * V) p = u * faceValue V p :=
  face_move_aux p hp u V

/-- The Haar prior really sees the face with the single-group Haar law. -/
lemma face_prior (hp : p.1 + step p.2.val.2 ≠ p.1)
    {g : G.El → ℝ} (hg : Continuous g) :
    (∫ V : Config G c, g (faceValue V p) ∂prior G c) = ∫ u : G.El, g u ∂G.probHaar := by
  have hi (V : Config G c) :
      (∫ u : G.El, g (faceValue (Pi.mulSingle (firstLink p) u * V) p) ∂G.probHaar) =
       ∫ u : G.El, g u ∂G.probHaar := by
    simp_rw [face_move p hp]
    exact (measurePreserving_mul_right G.probHaar (faceValue V p)).integral_comp
      ((Homeomorph.mulRight (faceValue V p)).measurableEmbedding) g
  rw [← move_integral (h:=fun V => g (faceValue V p)) (firstLink p)
    (hg.comp (show Continuous fun V : Config G c => faceValue V p from continuous_travel _ _))]
  simp_rw [hi]
  simp

private lemma moved_noise_estimate (hp : p.1 + step p.2.val.2 ≠ p.1)
    (hb : |β| ≤ B) (V Q : Config G c) {g : G.El → ℝ} (hg : Continuous g) (h0 : ∀ u, 0 ≤ g u) :
    noiseFloor B S.kernel.penalty * (∫ u, g u ∂G.probHaar) *
        (∫ u : G.El, S.noise β Q (Pi.mulSingle (firstLink p) u * V) ∂G.probHaar) ≤
      ∫ u : G.El, S.noise β Q (Pi.mulSingle (firstLink p) u * V) *
        g (faceValue (Pi.mulSingle (firstLink p) u * V) p) ∂G.probHaar := by
  let e := firstLink p
  let r (b : Edge (Site c)) (u : G.El) :=
    (S.penaltyZ β G)⁻¹ * S.penaltyWeight β (u * (Q b)⁻¹)
  let z := ∏ b ∈ Finset.univ.erase e, r b (V b)
  let a := noiseFloor B S.kernel.penalty
  have ha (b) (u) : a ≤ r b u := link_weight_ge S hb _
  have hz : 0 ≤ z := Finset.prod_nonneg fun b _ => (noiseFloor_pos _ _).le.trans (ha b _)
  have hsplit (u : G.El) : S.noise β Q (Pi.mulSingle (firstLink p) u * V) =
      z * r e (u * V e) := by
    let V' := Pi.mulSingle e u * V
    change (∏ b, r b (V' b)) = (∏ b ∈ Finset.univ.erase e, r b (V b)) * r e _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
    apply congrArg₂ (· * ·)
    · exact Finset.prod_congr rfl fun x hx => by
        simp_rw [V', Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.mem_erase.mp hx).1, one_mul]
    simp [V']
  have hright (H : G.El → ℝ) (w : G.El) :
      (∫ u : G.El, H (u*w) ∂G.probHaar) = ∫ u : G.El, H u ∂G.probHaar :=
    (measurePreserving_mul_right G.probHaar w).integral_comp
      ((Homeomorph.mulRight w).measurableEmbedding) H
  have hmass : (∫ u : G.El, S.noise β Q (Pi.mulSingle (firstLink p) u * V) ∂G.probHaar) = z := by
    simp_rw [hsplit]
    rw [integral_const_mul, hright]
    simp_rw [r]
    rw [integral_const_mul, hright (S.penaltyWeight β), ← StepData.penaltyZ,
      inv_mul_cancel₀ (S.penaltyZ_pos β).ne', mul_one]
  rw [hmass]; simp_rw [hsplit, face_move p hp, mul_assoc z]; rw [integral_const_mul, mul_comm _ z]
  refine mul_le_mul_of_nonneg_left ?_ hz
  rw [← hright g (faceValue V p), ← integral_const_mul]
  let g' (u : G.El) := g (u * faceValue V p)
  have hc : Continuous g' := hg.comp (continuous_id.mul continuous_const)
  refine integral_mono (μ:=G.probHaar)
    (((continuous_const (y:=noiseFloor B S.kernel.penalty)).mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (((show Continuous (fun u : G.El => r e (u * V e)) from ?_).mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (fun u => mul_le_mul_of_nonneg_right (ha _ _) (h0 _))
  exact continuous_const.mul
    ((S.penaltyWeight_cont β).comp ((continuous_id.mul continuous_const).mul continuous_const))

private lemma noise_cont_right (β : ℝ) (Q : Config G c) : Continuous (S.noise β Q) := by
  unfold StepData.noise StepData.penaltyWeight
  fun_prop

lemma noise_estimate_face (hp : p.1 + step p.2.val.2 ≠ p.1) (hb : |β| ≤ B)
    (Q : Config G c) {g : G.El → ℝ} (hg : Continuous g) (h0 : ∀ u, 0 ≤ g u) :
    noiseFloor B S.kernel.penalty * (∫ u, g u ∂G.probHaar) ≤
      ∫ V : Config G c, S.noise β Q V * g (faceValue V p) ∂prior G c := by
  let a := noiseFloor B S.kernel.penalty * (∫ u, g u ∂G.probHaar)
  have hn := noise_cont_right S β Q
  have ht : Continuous fun V : Config G c => S.noise β Q V * g (faceValue V p) :=
    hn.mul (hg.comp (show Continuous fun V : Config G c => faceValue V p from continuous_travel _ _))
  have h := move_mono (firstLink p) a hn ht (fun V => moved_noise_estimate S p hp hb V Q hg h0)
  rw [S.noise_mass, mul_one] at h
  exact h

lemma density_estimate_face (hp : p.1 + step p.2.val.2 ≠ p.1) (hb : |β| ≤ B)
    (h : S.patch.Branches S.kernel G) (U : Config G f) {g : G.El → ℝ}
    (hg : Continuous g) (h0 : ∀ u, 0 ≤ g u) :
    noiseFloor B S.kernel.penalty * (∫ u, g u ∂G.probHaar) ≤
      ∫ V, S.density β U V * g (faceValue V p) ∂prior G c := by
  simp_rw [StepData.density, Finset.sum_mul, mul_assoc (S.likelihood _ _)]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    calc
      _ = ∑ t, S.likelihood U t * (noiseFloor B S.kernel.penalty * (∫ u, g u ∂G.probHaar)) := by
        rw [← Finset.sum_mul, S.chosen h, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (noise_estimate_face S p hp hb _ hg h0) (S.likelihood_pos U i)
  intro i _
  have hn := noise_cont_right S β (S.prediction U i)
  have hs := (hn.mul (hg.comp
    (show Continuous fun V : Config G c => faceValue V p from continuous_travel _ _)))
  exact (hs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _

end Plaquette

section Variance

/-- Real normalized defining trace. -/
def normalizedTrace (u : SU.E) : ℝ := 1 - SU.group.price u

lemma normalizedTrace_trace (u : SU.E) :
    normalizedTrace u = (SU.fund u).trace.re / 5 := by
  unfold normalizedTrace Gauge.price
  change 1 - (1 - (SU.fund u).trace.re / ↑(5 : ℕ)) = _
  norm_num

@[fun_prop] lemma normalizedTrace_cont : Continuous normalizedTrace :=
  continuous_const.sub SU.group.continuous_price

lemma normalizedTrace_nonconstant : normalizedTrace SU.central ≠ normalizedTrace 1 := by
  intro h
  have hu : SU.central ≠ 1 := by
    intro hu
    have he := congrArg (fun U => SU.fund U 0 0) hu
    change Matrix.diagonal (fun _ : Fin 5 => SU.z) 0 0 = (1 : SU.group.Mat) 0 0 at he
    exact SU.z_prim.ne_one (by decide) (by simpa using he)
  have hmat : SU.group.mat SU.central - 1 ≠ 0 := sub_ne_zero_of_ne
    (show SU.group.mat SU.central ≠ SU.group.mat 1 from SU.group.mat_injective.ne hu)
  have he : 0 < SU.group.chord SU.central := div_pos (norm_pos_iff.mpr hmat)
    (Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos))
  simp [normalizedTrace] at h
  have := SU.group.chord_price SU.central
  nlinarith

local notation "μG" => SU.group.probHaar

def faceHaarVariance : ℝ :=
  ∫ u : SU.E, (normalizedTrace u - ∫ v, normalizedTrace v ∂μG)^2 ∂μG

theorem faceHaarVariance_pos : 0 < faceHaarVariance := by
  let m := ∫ v, normalizedTrace v ∂μG
  let g (u : SU.E) := (normalizedTrace u - m)^2
  have h : Continuous g := (normalizedTrace_cont.sub continuous_const).pow _
  change 0 < ∫ u, g u ∂μG
  apply (integral_pos_iff_support_of_nonneg (μ:=μG) (fun u => show 0 ≤ g u from sq_nonneg _)
    (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).2
  refine h.isOpen_support.measure_pos μG ?_
  by_cases hm : normalizedTrace 1 = m
  · exact ⟨SU.central, show g SU.central ≠ 0 from pow_ne_zero _
      (sub_ne_zero_of_ne (hm ▸ normalizedTrace_nonconstant))⟩
  exact ⟨1, show g 1 ≠ 0 from pow_ne_zero _ (sub_ne_zero_of_ne hm)⟩

private lemma squareIntegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w t : α → ℝ) (hw : Integrable w μ) (hwt : Integrable (fun u => w u * t u) μ)
    (hwt2 : Integrable (fun u => w u * t u^2) μ)
    (h1 : ∫ u, w u ∂μ = 1) (x : ℝ) :
    (∫ u, w u * (t u - x)^2 ∂μ) =
      (∫ u, w u * t u^2 ∂μ) - (∫ u, w u * t u ∂μ) * (2*x) + x^2 := by
  have H (u) : w u * (t u - x)^2 = w u * t u^2 - w u * t u * (2*x) + w u * x^2 := by ring
  simp_rw [H]; rw [integral_add
    (show Integrable (fun u => w u * t u^2 - w u * t u * (2*x)) μ from
      hwt2.sub (hwt.mul_const (2*x))) (hw.mul_const _),
    integral_sub hwt2 (hwt.mul_const _), integral_mul_const, integral_mul_const, h1, one_mul]

lemma faceHaarVariance_le (m : ℝ) :
    faceHaarVariance ≤ ∫ u, (normalizedTrace u - m)^2 ∂μG := by
  have he (a : ℝ) :
      (∫ u, (normalizedTrace u - a)^2 ∂μG) =
        (∫ u, normalizedTrace u^2 ∂μG) - (∫ u, normalizedTrace u ∂μG) * (2*a) + a^2 := by
    simpa using squareIntegral (μ:=μG) (fun _ => 1) normalizedTrace (integrable_const _)
      (by
        simp_rw [one_mul]
        exact normalizedTrace_cont.integrable_of_hasCompactSupport (μ:=μG)
          (HasCompactSupport.of_compactSpace _))
      (by
        simp_rw [one_mul]
        exact (normalizedTrace_cont.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (by simp) a
  rw [faceHaarVariance, he, he]
  nlinarith [sq_nonneg (m - ∫ u, normalizedTrace u ∂μG)]

/-- Strict (positive RHS budget on the lower-bound side), pointwise, volume-uniform once
`B` and penalty are fixed. Uses the **paid step's** mixture weights. -/
lemma conditional_variance_face {c f : Side} (S : StepData c f) (p : Face (Per c))
    (hp : p.1 + step p.2.val.2 ≠ p.1)
    {β B : ℝ} (hb : |β| ≤ B) (h : S.patch.Branches S.kernel SU.group) (U : Config SU.group f) :
    noiseFloor B S.kernel.penalty * faceHaarVariance ≤
      (∫ V, S.density β U V * (normalizedTrace (faceValue V p))^2 ∂prior SU.group c) -
      (∫ V, S.density β U V * normalizedTrace (faceValue V p) ∂prior SU.group c)^2 := by
  let q := prior SU.group c
  let w := S.density β U
  let t (V : Config SU.group c) := normalizedTrace (faceValue V p)
  have hw : Continuous w := by
    unfold w StepData.density
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (noise_cont_right S β _)
  have ht : Continuous t := normalizedTrace_cont.comp
    (show Continuous fun V : Config SU.group c => faceValue V p from continuous_travel _ _)
  let m := ∫ V, w V * t V ∂q
  let g (u : SU.E) := (normalizedTrace u - m)^2
  have hg : Continuous g := (normalizedTrace_cont.sub continuous_const).pow _
  refine (mul_le_mul_of_nonneg_left (faceHaarVariance_le m) (noiseFloor_pos _ _).le).trans
    ((density_estimate_face S p hp hb h U hg (fun u => sq_nonneg _)).trans_eq ?_)
  change (∫ V, w V * (t V - m)^2 ∂prior SU.group c) =
    (∫ V, w V * (t V)^2 ∂prior SU.group c) - m^2
  rw [squareIntegral w t (S.density_integrable ..)
    ((hw.mul ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hw.mul (ht.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (S.density_total h β U)]
  change _ - m * (2*m) + m^2 = _
  ring

end Variance

end YM.CF.SatinRotation
#print axioms YM.CF.SatinRotation.conditional_variance_face
#print axioms YM.CF.SatinRotation.faceHaarVariance_pos
