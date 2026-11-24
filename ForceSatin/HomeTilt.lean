import Verses.Ocean

/-! Basis-free Fock lemmas for the exact WA.1 tilt, and for its use in tilted
    checker products (cf. WA.6–11). Conventions throughout: counting norm, linear
    in second slot of inner product, `Γ` = Fock.quant.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Cascade Thera Verses
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {I : Type} [LinearOrder I] [Fintype I] {P Q : Op I} (p : IsStarProjection P)

/-- One-particle tilt symbol ($V_t$ its exponent). -/
def tiltSymbol (P : Op I) : Op I := (1-P)-P

include p
theorem tiltReal : IsSelfAdjoint (tiltSymbol P) := p.one_sub.isSelfAdjoint.sub p.isSelfAdjoint

def rankPrice (P : Op I) := P.trace.re
/-- rank(P)·1 + dg(1-2P). -/
def excitation (P : Op I) : FC I := rankPrice P • 1 + dg (tiltSymbol P)

theorem excitation_real : IsSelfAdjoint (excitation P) := by
  have hs : IsSelfAdjoint (dg (tiltSymbol P)) := by
    unfold IsSelfAdjoint; rw [← dg_star,(tiltReal p).star_eq]
  apply IsSelfAdjoint.add _ hs
  unfold IsSelfAdjoint; simp only [star_smul,star_one,star_trivial]

/-- exact Fock tilt, including rank normalization. -/
lemma tilt_quant_exp (t : ℝ) : grow (excitation P) t =
    Real.exp (t * rankPrice P) • quant (grow (tiltSymbol P) t) := by
  rw [ferment (tiltReal p),grow,excitation,smul_add, smul_smul]
  let T : FC I := 1
  let c := t*rankPrice P
  letI : NormedAlgebra ℚ (FC I) := NormedAlgebra.restrictScalars ℚ ℂ (FC I)
  rw [exp_add_of_commute ((Commute.one_left _).smul_left (t * rankPrice P))]
  have he (J : Type) [DecidableEq J] [Fintype J] : exp (c • (1 : Op J)) = Real.exp c • 1 := by
    rw [show c • (1 : Op J)= Matrix.diagonal (fun _=> (c:ℂ)) from ?_, phase_diag]
    all_goals ext i j; by_cases e:i=j <;> simp [e,Complex.real_smul,Complex.ofReal_exp]
  rw [he (Finset I), Algebra.smul_mul_assoc, one_mul]

/-- Rank multiplier for the (so far *unqualified*) sector state.
Changed configurations can have different ranks! -/
lemma scalar_quant_line (c : ℝ) :
    quant (Real.exp c • (1 : Op I)) * lineOp P = Real.exp (c * rankPrice P) • lineOp P := by
  obtain ⟨U,s,rfl⟩ := spot_projection P p
  rw [line_twist,rankPrice,trace_twist,trace_cut]
  let D := quantU U; let W : Op I := Real.exp c • 1
  have he : twist D (quant W) = quant W := by rw [←quant_twist]; simp only [W,map_smul,map_one]
  let Y : FC I := lineOp (cutM s)
  change quant W * twist D Y = Real.exp _ • twist D Y
  nth_rw 1 [←he]
  rw [←map_mul,←map_smul]
  apply congrArg
  unfold W Y; rw [show Real.exp c • (1 : Op I) = Matrix.diagonal (fun _=> (Real.exp c:ℂ)) from ?_, quant_diag, cutLine]
  · ext i j; rw [cutM,Matrix.diagonal_mul_diagonal]
    by_cases h : i=j
    · subst j; by_cases hh : i=s
      · subst s; simp only [Matrix.diagonal_apply_eq, mem_singleton,ite_true,mul_one, Matrix.smul_apply]; rw [Complex.real_smul]; simp [mul_comm c, Real.exp_nat_mul]
      simp [hh]
    simp [h]
  ext i j; by_cases e:i=j <;> simp [e,Complex.real_smul]

omit p in
lemma acts_scalar {U : Type} [DecidableEq U] [Fintype U] (r : ℝ) (A : Op U) (x : Ket U) : acts (r • A) x = r • acts A x := by
  simp_rw [← Complex.coe_smul]
  exact act_smul ..

lemma scalar_quant_acts (c : ℝ) (A : Op I) (x : Wave I) (h : Sea P x) :
    acts (quant (Real.exp c • A)) x = Real.exp (c * rankPrice P) • acts (quant A) x := by
  rw [show Real.exp c • A = A*(Real.exp c • 1) from by rw [Algebra.mul_smul_comm,mul_one],quant_mul,act_mul]
  nth_rw 1 [←h.1]
  rw [←act_mul _ (lineOp P),scalar_quant_line p c,acts_scalar,h.1]
  exact ((acts (quant A)).map_smul_of_tower ..)

def tilt (P : Op I) (t : ℝ) : Shaft I where
  sell := grow (tiltSymbol P) t
  buy := grow (tiltSymbol P) (-t)
  payment := by simp only [grow,neg_smul]; exact wind_inv _

lemma tilt_on_line (t : ℝ) : (tilt P t).sell * P = Real.exp (-t) • P := by
  obtain ⟨U,s,rfl⟩ := spot_projection P p
  rw [tilt]
  dsimp only
  let S := cutM s
  have he : tiltSymbol (twist U S)=twist U (tiltSymbol S) := by rw [tiltSymbol,tiltSymbol,map_sub,map_sub,map_one]
  have hv : t • tiltSymbol (cutM s)=Matrix.diagonal (fun i=> (↑(if i∈s then -t else t : ℝ) : ℂ)) := by
    ext i j; by_cases h:i=j
    · subst j; by_cases y:i∈s <;> simp [y,tiltSymbol,cutM,Complex.real_smul]
    simp [h,cutM,tiltSymbol]
  change grow (tiltSymbol _) t * twist U S=_ • twist U S
  rw [grow,he,←map_smul, ←breeze_exp, ←map_mul, ←map_smul]; apply congrArg
  unfold S; rw [hv,phase_diag,cutM,Matrix.diagonal_mul_diagonal]
  ext i j; by_cases e:i=j
  · subst j; by_cases he:i∈s <;> simp [he,Complex.real_smul,Complex.ofReal_exp]
  simp [e]


variable [Nonempty I]

open CF.Window

omit p in
-- same norm implementation as Graph.bootC, here on single-particle matrices
lemma norm_exp_le (A : Op I) : ‖exp A‖ ≤ Real.exp ‖A‖ := by
  rw [congrFun (exp_eq_tsum ℝ), Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact norm_expSeries_summable' (𝕂:=ℝ) A
  exact Summable.tsum_mono (norm_expSeries_summable' (𝕂:=ℝ) A) (by
    apply Summable.of_norm; exact norm_expSeries_summable' (𝕂:=ℝ) ‖A‖)
    (fun n=> by rw [norm_smul,Real.norm_of_nonneg (by positivity)]
                exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity))

def tiltCost := Real.exp 2

lemma tilt_norm {t : ℝ} (h : |t| ≤ 1) : ‖(tilt P t).sell‖ ≤ tiltCost := by
  have x := norm_exp_le (t • tiltSymbol P)
  apply x.trans (Real.exp_le_exp.mpr ?_)
  rw [norm_smul,Real.norm_eq_abs]
  apply (mul_le_of_le_one_left (norm_nonneg _) h).trans
  unfold tiltSymbol
  exact (norm_sub_le ..).trans ((add_le_add (p.one_sub.norm_le _) (p.norm_le _)).trans_eq one_add_one_eq_two)

omit p in
theorem composite_fiber (T S : Shaft I) {b c : ℝ} (h : fiber S b) (u : 0 ≤ c)
    (x : ‖T.sell‖ ≤ c) (y : ‖T.buy‖ ≤ c) : fiber (T.foldC S) (c*b) := by
  constructor <;> intro i <;> unfold Shaft.foldC; dsimp only
  · rw [act_mul]; exact (Flare.opy ..).trans (mul_le_mul x (h.fst i) (norm_nonneg _) u)
  rw [star_mul,act_mul]; exact (Flare.opy ..).trans (mul_le_mul ((norm_star _).trans_le y) (h.snd i) (norm_nonneg _) u)

lemma tilt_fiber (T : Shaft I) {b t : ℝ} (h : fiber T b) (u : |t| ≤ 1) :
    fiber ((tilt P t).foldC T) (tiltCost*b) :=
  composite_fiber _ _ h (Real.exp_pos _).le (tilt_norm p u) (tilt_norm (t:= -t) p (by rwa [abs_neg]))

omit p [Nonempty I] in
theorem rank_budget (t : ℝ) (u : |t| ≤ 1) : t * (rankPrice P - rankPrice Q) ≤ entryBudget (Q-P) := by
  have he := entry_dot ((-t) • (1 : Op I)) (Q-P) 1 (fun i j=>?_)
  · rw [Algebra.smul_mul_assoc,one_mul, Matrix.trace_smul, Matrix.trace_sub,one_mul] at he
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im, zero_mul,sub_zero,
      Complex.sub_re] at he
    unfold rankPrice; linarith
  simp only [Matrix.smul_apply,norm_smul,norm_neg, Real.norm_eq_abs]
  apply (mul_le_of_le_one_right (abs_nonneg _) ?_).trans u
  rw [Matrix.one_apply]; split <;> simp

def tiltScale (t : ℝ) : Shaft I := ⟨Real.exp t • 1, Real.exp (-t) • 1, by
  rw [Algebra.smul_mul_assoc,one_mul, smul_smul,←Real.exp_add, add_neg_cancel,Real.exp_zero,one_smul]⟩

def tiltRaisedCost (b : ℝ) := Real.exp 1 * (tiltCost * b)

lemma raised_budget (T : Shaft I) {b t : ℝ} (h : fiber T b) (u : |t| ≤ 1) :
    fiber ((tiltScale t).foldC ((tilt P t).foldC T)) (tiltRaisedCost b) := by
  apply composite_fiber _ _ (tilt_fiber p T h u) (Real.exp_pos 1).le
  · unfold tiltScale; dsimp only; rw [norm_smul, norm_one,Real.norm_of_nonneg (Real.exp_pos _).le,mul_one]
    exact Real.exp_monotone ((le_abs_self _).trans u)
  unfold tiltScale; dsimp only; rw [norm_smul, norm_one,Real.norm_of_nonneg (Real.exp_pos _).le,mul_one]; exact Real.exp_monotone ((neg_le_abs _).trans u)

def tiltRent (b : ℝ) := 1 + ((tiltRaisedCost b)^2+1)/2

theorem tilt_bound_sea (T : Shaft I) {b t : ℝ} (c : fiber T b) (d : 0 ≤ b) (u : T.sell*P=P)
    (v : |t| ≤ 1) (q : IsStarProjection Q) (y : Wave I) (hy : Sea Q y) :
    ‖acts (grow (excitation P) t) (acts (quant T.sell) y)‖ ≤ Real.exp (tiltRent b*entryBudget (Q-P)) := by
  let L := (tilt P t).foldC T
  let R := (tiltScale t).foldC L
  let k := tiltRaisedCost b
  have hk : 0≤k := by unfold k tiltRaisedCost tiltCost; positivity
  have he : L.sell*P=Real.exp (-t) • P := by
    unfold L Shaft.foldC
    dsimp only
    rw [mul_assoc,u,tilt_on_line p]
  have hr : R.sell=Real.exp t • L.sell := by unfold R tiltScale Shaft.foldC; dsimp only; rw [Algebra.smul_mul_assoc,one_mul]
  have ht : R.sell*P=P := by rw [hr,Algebra.smul_mul_assoc,he,smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
  have hw : acts (grow (excitation P) t) (acts (quant T.sell) y) = Real.exp (t*(rankPrice P - rankPrice Q)) • acts (quant R.sell) y := by
    rw [hr,scalar_quant_acts q t _ _ hy,smul_smul,←Real.exp_add,show t*(rankPrice P-rankPrice Q)+t*rankPrice Q=t*rankPrice P from by ring]
    rw [tilt_quant_exp p,acts_scalar,←act_mul,←quant_mul]; rfl
  rw [hw,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left (attacking R P p ht (raised_budget p T c v) hk Q q y hy) (Real.exp_pos _).le).trans
  rw [←Real.exp_add]; apply Real.exp_monotone; unfold tiltRent; linarith only [rank_budget t v (P:=P) (Q:=Q)]
-- audit later

end YM.CF.Papyrus.Franc.SatinForce
