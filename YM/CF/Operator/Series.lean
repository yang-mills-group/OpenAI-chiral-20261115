import YM.CF.Operator.SignScalar
import YM.CF.Operator.Spectral

/-!
# Chiral projector, with norm-rate bound

On the specified band `polarity` is sign(H). On the whole operator space we choose a
series definition (no star), useful also on complex neighborhoods of the band.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false

def slack (A : Op n) := (1 : Op n) - (1/256 : ℝ) • A^2

def rsTerm (A : Op n) (k : ℕ) := SignScalar.c k • (slack A)^k

def rsEval (A : Op n) := ∑' k : ℕ, rsTerm A k

def polarity (A : Op n) := ((1/16 : ℝ) • A) * rsEval A

def projector (A : Op n) := (1/2 : ℝ) • (1 + polarity A)

@[fun_prop] lemma continuous_slack : Continuous (slack (n:=n)) := by unfold slack; fun_prop
@[fun_prop] lemma continuous_rsTerm (k) : Continuous (rsTerm (n:=n) · k) := by unfold rsTerm; fun_prop

variable {A : Op n} {r : ℝ}
lemma rsTerm_bound (h : ‖slack A‖ ≤ r) (k : ℕ) : ‖rsTerm A k‖ ≤ r^k := by
  rw [rsTerm,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (SignScalar.c_norm _)).trans <|
    (norm_pow_le ..).trans <| pow_le_pow_left₀ (norm_nonneg _) h _
lemma rs_sum (h : ‖slack A‖ < 1) : HasSum (rsTerm A) (rsEval A) :=
  ((summable_geometric_of_lt_one (norm_nonneg _) h).of_norm_bounded (rsTerm_bound le_rfl)).hasSum
lemma continuousOn_rsEval (hr : r < 1) (hr' : 0 ≤ r) :
    ContinuousOn (rsEval (n:=n)) {A : Op n | ‖slack A‖ ≤ r} :=
  continuousOn_tsum (fun i => (continuous_rsTerm i).continuousOn) (summable_geometric_of_lt_one hr' hr)
    fun i _ h => rsTerm_bound h i
lemma continuousOn_projector (hr : r < 1) (hr' : 0 ≤ r) :
    ContinuousOn (projector (n:=n)) {A : Op n | ‖slack A‖ ≤ r} := by
  exact ContinuousOn.smul (continuousOn_const (c:= (1/2 : ℝ))) (ContinuousOn.add (continuousOn_const (c:= (1:Op n))) (ContinuousOn.mul
    (ContinuousOn.smul (continuousOn_const (c:=(1/16:ℝ))) continuousOn_id) (continuousOn_rsEval hr hr')))

lemma rs_tail (k : ℕ) (h : ‖slack A‖ ≤ r) (hr : r < 1) :
    ‖rsEval A - ∑ i ∈ Finset.range k, rsTerm A i‖ ≤ r^k * (1-r)⁻¹ := by
  have hn := (norm_nonneg _).trans h
  have hs := summable_geometric_of_lt_one hn hr
  have ht := (summable_nat_add_iff k).mpr hs
  have ha := ht.of_nonneg_of_le (fun i : ℕ => norm_nonneg (rsTerm A (i+k))) (fun i => rsTerm_bound h (i+k))
  unfold rsEval; rw [← (rs_sum (h.trans_lt hr)).summable.sum_add_tsum_nat_add k, add_sub_cancel_left]
  calc
    _ ≤ _ := norm_tsum_le_tsum_norm ha
    _ ≤ ∑' i : ℕ, r^(i+k) := ha.tsum_le_tsum (fun _ => rsTerm_bound h _) ht
    _ = _ := by simp_rw [pow_add]; rw [tsum_mul_right, tsum_geometric_of_lt_one hn hr,mul_comm]

def rsApprox (A : Op n) (k : ℕ) := ∑ i ∈ Finset.range k, rsTerm A i

def approxP (A : Op n) (k : ℕ) := (1/2 : ℝ) • (1 + ((1/16 : ℝ) • A) * rsApprox A k)

lemma projector_tail (k : ℕ) (h : ‖slack A‖ ≤ r) (hr : r < 1) :
    ‖projector A - approxP A k‖ ≤ (‖A‖ / 32) * (r^k * (1-r)⁻¹) := by
  unfold projector approxP polarity; rw [← smul_sub,add_sub_add_left_eq_sub, ← mul_sub,norm_smul]
  calc
    _ ≤ ‖(1/2:ℝ)‖ * (‖(1/16:ℝ) • A‖ * (r^k * (1-r)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (rs_tail k h hr) (norm_nonneg _))
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num),Real.norm_of_nonneg (by norm_num)]; ring

/-- Band used in the cutoff theorem. From sufficiently small plaquette cap. -/
structure Safe (A : Op n) : Prop where
  self : IsSelfAdjoint A
  bound : ‖A‖ ≤ 16
  margin : (1/2 : ℝ) • (1 : Op n) ≤ A^2

def rho : ℝ := 511/512
lemma rho_pos : 0 < rho := by unfold rho; positivity
lemma rho_lt : rho < 1 := by unfold rho; norm_num

lemma Safe.slack_nn (h : Safe A) : 0 ≤ slack A := by
  have hb : ‖A^2‖ ≤ 256 := (norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) h.bound 2).trans (by norm_num))
  have hs := h.self.pow 2
  unfold slack; apply sub_nonneg.mpr
  calc
    _ ≤ (1/256:ℝ) • ((256:ℝ) • (1:Op n)) := smul_le_smul_of_nonneg_left
      ((op_le_norm_one hs).trans (smul_le_smul_of_nonneg_right hb zero_le_one)) (by norm_num)
    _ = _ := by rw [smul_smul]; norm_num
lemma Safe.slack_le (h : Safe A) : slack A ≤ rho • (1 : Op n) := by
  unfold slack
  calc
    _ ≤ (1:Op n)-(1/256:ℝ) • ((1/2 : ℝ) • (1:Op n)) :=
      sub_le_sub_left (smul_le_smul_of_nonneg_left h.margin (by norm_num)) _
    _ = _ := by unfold rho; module
lemma Safe.good (h : Safe A) : ‖slack A‖ ≤ rho := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ rho_pos.le h.slack_nn).mpr
  convert! h.slack_le
  rw [Algebra.algebraMap_eq_smul_one]

open SignScalar
variable (U : UNI n) (d : n → ℝ)
def eigSlack (d : n → ℝ) := 1 - (1/256:ℝ) • d^2
lemma slack_spectral : slack (spectral U d) = spectral U (eigSlack d) := by
  rw [slack,eigSlack,spectral_pow, spectral_smul, ← spectral_sub, spectral_one]
lemma rs_spectral (h : Safe (spectral U d)) : rsEval (spectral U d) = spectral U (bin ∘ eigSlack d) := by
  let R := eigSlack d
  have he := h.slack_nn
  have ht := h.slack_le
  rw [slack_spectral, ← spectral_zero U,spectral_le] at he
  rw [slack_spectral,← spectral_one U,spectral_smul,spectral_le] at ht
  let F : ℕ → n → ℝ := fun k => c k • R^k
  have hf : HasSum F (bin ∘ R) := by
    rw [Pi.hasSum]
    intro i
    have hn : 0 ≤ R i := he i
    have hb : R i ≤ rho := by simpa [R] using ht i
    have hs := (bin_summable _ (by rw [Real.norm_of_nonneg hn]; exact hb.trans_lt rho_lt)).of_norm
    simpa [F, bin] using hs.hasSum
  let L : (n → ℝ) →ₗ[ℝ] Op n :=
    { toFun := spectral U, map_add' := fun x y => (spectral_add ..).symm, map_smul' := fun x y => (spectral_smul ..).symm }
  have hb := hf.map L L.continuous_of_finiteDimensional
  apply (rs_sum (h.good.trans_lt rho_lt)).unique
  convert hb using 1
  · ext1 k; change rsTerm _ _ = spectral U _
    rw [rsTerm,slack_spectral,spectral_pow,spectral_smul]
  rfl

lemma sign_eval (x : ℝ) (h : 0 ≤ 1-x^2/256) (hh : 1-x^2/256 < 1) :
    (1/16*x) * bin (1-x^2/256) = if 0 < x then 1 else -1 := by
  have hn : x ≠ 0 := by intro hz; rw [hz] at hh; norm_num at hh
  have he := bin_sq _ h hh; have hp := bin_nonneg _ h
  have hb : ((1/16*x) * bin (1-x^2/256)) ^ 2 = 1 := by
    rw [mul_pow,he,show 1-(1-x^2/256)=x^2/256 by ring]; field_simp; ring
  rcases lt_or_gt_of_ne hn with hx|hx
  · rw [if_neg hx.not_gt]; nlinarith [mul_nonpos_of_nonpos_of_nonneg (show 1/16*x ≤ 0 by linarith) hp]
  · rw [if_pos hx]; nlinarith [mul_nonneg (show 0 ≤ 1/16*x by linarith) hp]

def signRoles (d : n → ℝ) : n → ℝ := fun i => if 0 < d i then 1 else -1
def occ (d : n → ℝ) : n → ℝ := fun i => if 0 < d i then 1 else 0
lemma polarity_spectral (h : Safe (spectral U d)) : polarity (spectral U d) = spectral U (signRoles d) := by
  rw [polarity,rs_spectral _ _ h,spectral_smul,spectral_mul]
  apply congrArg (spectral U); funext i
  have he := h.slack_nn; have ht := h.slack_le
  rw [slack_spectral, ← spectral_zero U,spectral_le] at he
  rw [slack_spectral,← spectral_one U,spectral_smul,spectral_le] at ht
  have hi (i:n) : eigSlack d i=1-(d i)^2/256 := by simp [eigSlack]; ring
  have hs : eigSlack d i ≤ rho := by simpa using ht i
  change 1/16*d i*bin (eigSlack d i) = _
  rw [hi]
  apply sign_eval _
  · rw [← hi]; exact he i
  rw [← hi]; exact hs.trans_lt rho_lt

lemma projector_spectral (h : Safe (spectral U d)) : projector (spectral U d) = spectral U (occ d) := by
  rw [projector,polarity_spectral _ _ h,← spectral_one U,spectral_add,spectral_smul]
  apply congrArg (spectral U); funext i
  by_cases hp : 0 < d i <;> norm_num [hp,signRoles,occ]
lemma Safe.projection (h : Safe A) : IsStarProjection (projector A) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A h.self
  rw [projector_spectral _ _ h]
  constructor
  · change spectral U _ * spectral U _ = _
    rw [spectral_mul]; apply congrArg (spectral U); funext i
    by_cases hp : 0 < d i <;> simp [occ,hp]
  exact spectral_adjoint ..
end YM.CF
