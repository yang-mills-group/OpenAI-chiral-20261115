import YM.CF.Operator.Series

/-! Perturbation on a common operator band. This handles approximate
intertwining by the antiunitary **pairing** on varying gauge/site data. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF
open scoped MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Cumulative Lipschitz estimate on the norm-band; constants need not be optimal. -/
lemma pow_near {r : ℝ} {A B : Op n} (_hr : 0 ≤ r) (ha : ‖A‖ ≤ r) (hb : ‖B‖ ≤ r) (k : ℕ) :
    ‖A^k - B^k‖ ≤ k*r^(k-1)*‖A-B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k =>
      let j := k+1
      let Δ := ‖A-B‖
      rw [pow_succ A (k+1),pow_succ B (k+1)]
      rw [show A^(k+1)*A-B^(k+1)*B = (A^j-B^j)*B + A^j*(A-B) by simp only [j,mul_sub,sub_mul]; abel]
      calc
        _ ≤ ((j*r^(j-1)*Δ)*r) + r^j*Δ := (norm_add_le ..).trans <| add_le_add
          ((norm_mul_le ..).trans (mul_le_mul ih hb (norm_nonneg _) ((norm_nonneg _).trans ih)))
          ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_pow_le ..).trans
            (pow_le_pow_left₀ (norm_nonneg A) ha j)) (norm_nonneg _)))
        _ = _ := by simp only [j,Δ, Nat.cast_add, Nat.cast_one,Nat.add_sub_cancel,pow_succ]; ring
lemma rs_near_term {A B : Op n} {r : ℝ} (h : 0 ≤ r) (ha : ‖slack A‖ ≤ r) (hb : ‖slack B‖ ≤ r) (k : ℕ) :
    ‖rsTerm A k - rsTerm B k‖ ≤ k*r^(k-1)*‖slack A-slack B‖ := by
  rw [rsTerm,rsTerm,← smul_sub,norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (SignScalar.c_norm _)).trans <| pow_near h ha hb k
lemma rs_eval_bound {A : Op n} {r : ℝ} (hr : r < 1) (h : ‖slack A‖ ≤ r) : ‖rsEval A‖ ≤ (1-r)⁻¹ := by
  simpa only [Finset.range_zero,Finset.sum_empty, sub_zero,pow_zero,one_mul] using rs_tail 0 h hr
lemma rs_near {A B : Op n} {r : ℝ} (hr : 0 < r) (hr' : r < 1) (ha : ‖slack A‖ ≤ r) (hb : ‖slack B‖ ≤ r) :
    ‖rsEval A - rsEval B‖ ≤ (1-r)⁻¹ ^ 2 * ‖slack A-slack B‖ := by
  let X : ℕ → ℝ := fun k => k*r^(k-1)
  have hx : HasSum X ((1-r)⁻¹ ^ 2) := by
    -- from shifted derivative of geometric
    have hs := (hasSum_coe_mul_geometric_of_norm_lt_one (r:=r) (by rwa [Real.norm_of_nonneg hr.le])).mul_left r⁻¹
    convert! hs using 1
    · funext i; cases i with
      | zero => simp [X]
      | succ i => simp only [X, pow_succ, Nat.add_sub_cancel]; field_simp
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hr.ne',one_mul,inv_pow]
  let d := ‖slack A - slack B‖
  have hd := hx.mul_right d
  have hs := (rs_sum (ha.trans_lt hr')).sub (rs_sum (hb.trans_lt hr'))
  have hfin := hd.summable.of_nonneg_of_le (fun k => norm_nonneg (rsTerm A k - rsTerm B k)) (rs_near_term hr.le ha hb)
  calc
    _ = ‖∑' k, (rsTerm A k - rsTerm B k)‖ := by rw [hs.tsum_eq]
    _ ≤ _ := norm_tsum_le_tsum_norm hfin
    _ ≤ ∑' k, X k*d := hfin.tsum_le_tsum (rs_near_term hr.le ha hb) hd.summable
    _ = _ := hd.tsum_eq
lemma slack_near {A B : Op n} {K : ℝ} (ha : ‖A‖ ≤ K) (hb : ‖B‖ ≤ K) :
    ‖slack A - slack B‖ ≤ K/128 * ‖A-B‖ := by
  rw [slack,slack, sub_sub_sub_cancel_left,norm_sub_rev,← smul_sub,norm_smul]
  calc
    _ ≤ ‖(1/256:ℝ)‖ * (↑(2:ℕ)*K^(2-1:ℕ)*‖A-B‖) := mul_le_mul_of_nonneg_left
      (pow_near ((norm_nonneg _).trans ha) ha hb 2) (norm_nonneg _)
    _ = _ := by rw [Real.norm_of_nonneg (by norm_num)]; norm_num; ring
lemma proj_near {A B : Op n} {r K : ℝ} (hr : 0 < r) (hr' : r < 1)
    (hs : ‖slack A‖ ≤ r) (ht : ‖slack B‖ ≤ r) (ha : ‖A‖ ≤ K) (hb : ‖B‖ ≤ K) :
    ‖projector A - projector B‖ ≤
        (1/32*((1-r)⁻¹+K*((1-r)⁻¹^2 * (K/128))))*‖A-B‖ := by
  unfold projector polarity
  rw [← smul_sub, add_sub_add_left_eq_sub,Algebra.smul_mul_assoc,
    Algebra.smul_mul_assoc,← smul_sub,smul_smul,norm_smul]
  have hx := (rs_near hr hr' hs ht).trans (mul_le_mul_of_nonneg_left (slack_near ha hb) (by positivity))
  calc
    _ ≤ (1/32)*(‖A-B‖*(1-r)⁻¹ + K*((1-r)⁻¹^2 * (K/128 * ‖A-B‖))) := by
      rw [show ‖(1/2:ℝ)*(1/16)‖=1/32 by rw [Real.norm_of_nonneg (by norm_num)]; ring,
        show A * rsEval A - B * rsEval B = (A-B)*rsEval B + A*(rsEval A-rsEval B) by
          rw [sub_mul,mul_sub]; abel]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans <|
        mul_le_mul_of_nonneg_left (rs_eval_bound hr' ht) (norm_nonneg _)) ((norm_mul_le ..).trans <|
        mul_le_mul ha hx (norm_nonneg _) ((norm_nonneg _).trans ha)))
    _ = _ := by ring

lemma Safe.proj_near {A B : Op n} (ha : Safe A) (hb : Safe B) :
    ‖projector A-projector B‖ ≤ 16400 * ‖A-B‖ := by
  convert CF.proj_near rho_pos rho_lt ha.good hb.good ha.bound hb.bound using 2
  norm_num [rho]

lemma Safe.twisted {A : Op n} (ha : Safe A) (U : UNI n) : Safe (twist U A) :=
  ⟨by rw [isSelfAdjoint_iff, ← map_star, ha.self.star_eq], by rw [twist_norm]; exact ha.bound,
    by
      conv_rhs => rw [← map_pow]
      apply le_trans ?_ (twist_mono U ha.margin)
      rw [map_smul, map_one]⟩
lemma twist_spectral (V U : UNI n) (d : n → ℝ) : twist V (spectral U d) = spectral (V*U) d := by
  unfold spectral twist; rw [map_mul]; rfl
lemma projector_twist {A : Op n} (ha : Safe A) (U : UNI n) : twist U (projector A) = projector (twist U A) := by
  obtain ⟨V,d,rfl⟩ := spectral_exists A ha.self
  have ht := ha.twisted U; rw [twist_spectral] at ht
  rw [projector_spectral V d ha,twist_spectral,twist_spectral,projector_spectral _ _ ht]

def ccU (U : UNI n) : UNI n := ⟨cc U.val,by
  have H : star U.val * U.val = 1 := U.property.1
  have Q : U.val * star U.val = 1 := U.property.2
  constructor <;> rw [← cc_star, ← cc_mul] <;> simp only [H,Q,cc_one]⟩
lemma cc_spectral (U : UNI n) (d : n → ℝ) : cc (spectral U d) = spectral (ccU U) d := by
  simp only [spectral, twist_formula,cc_mul, cc_star,ccU]
  congr 2
  ext i j; by_cases h:i=j <;> simp [h]
lemma Safe.conjugated {A : Op n} (ha : Safe A) : Safe (cc A) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A ha.self
  rw [cc_spectral]
  refine ⟨spectral_adjoint .., ?_, ?_⟩
  · simpa only [spectral,twist_norm] using ha.bound
  have h := ha.margin
  rw [spectral_pow, ← spectral_one U,spectral_smul,spectral_le] at h
  rwa [spectral_pow, ← spectral_one (ccU U),spectral_smul,spectral_le]
lemma projector_cc {A : Op n} (ha : Safe A) : projector (cc A) = cc (projector A) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists A ha.self
  have ht := ha.conjugated; rw [cc_spectral] at ht
  rw [projector_spectral U d ha,cc_spectral,cc_spectral,projector_spectral _ _ ht]

lemma twist_sub (U : UNI n) (A B : Op n) : ‖A - twist U B‖ = ‖A * U.val - U.val * B‖ := by
  rw [← CStarRing.norm_mul_coe_unitary (A-twist U B) U]; change ‖(A-twist U B)*U.val‖=_
  rw [sub_mul,twist_formula,mul_assoc (U.val*B),show star U.val * U.val = 1 from U.property.1,mul_one]
lemma Safe.antiunitary {A : Op n} (ha : Safe A) (U : UNI n) :
    ‖projector A * U.val-U.val * cc (projector A)‖ ≤ 16400 * ‖A * U.val-U.val * cc A‖ := by
  rw [← projector_cc ha, ← twist_sub, projector_twist ha.conjugated, ← twist_sub]
  exact ha.proj_near (ha.conjugated.twisted U)
end YM.CF
