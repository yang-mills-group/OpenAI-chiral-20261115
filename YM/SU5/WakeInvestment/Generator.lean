import YM.CF.Fock.Semig

/-!
Part WA (Wickers): seam price with the *positive excitation tilt*. All the following are at
literal finite-regulator Fock space (including wrong degrees, `Wave` on all the subsets).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Fock Lattice Finset NormedSpace
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {P Q B : Op I}

/-- The operator $N$ of WA. `P` here will be the *flat Sea projector* on Single. -/
def excit (P : Op I) : FC I := P.trace.re • 1 + dg (1-P-P)

def wholeTilt (P : Op I) (t : ℝ) := exp (t • excit P)

/-- `V_t=exp(t*(1-2*S0))` at exactly that flat compensated bill. -/
def oneTilt (P : Op I) (t : ℝ) : Op I := Fock.grow (1-P-P) t

/-- Keep both signs; will compare also operators before multiplying them into the pressure.
No rank matching of the true Loom Sea with the flat one is needed. -/
theorem tilt_spec (p : IsStarProjection P) (t : ℝ) :
    wholeTilt P t = (Real.exp (t*P.trace.re)) • quant (oneTilt P t) := by
  have u : IsSelfAdjoint (1-P-P) := p.one_sub.isSelfAdjoint.sub p.isSelfAdjoint
  rw [oneTilt,ferment u]
  unfold wholeTilt excit
  letI : NormedAlgebra ℚ (FC I) := NormedAlgebra.restrictScalars ℚ ℂ (FC I)
  rw [smul_add, smul_smul, exp_add_of_commute ?_]
  · rw [←Algebra.algebraMap_eq_smul_one,←algebraMap_exp_comm,←Real.exp_eq_exp_ℝ,Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]
  exact (Commute.one_left _).smul_left _

lemma oneTilt_price (p : IsStarProjection P) (t : ℝ) :
    oneTilt P t = Real.exp (-t) • P + Real.exp t • (1-P) := by
  obtain ⟨U,s,rfl⟩ := spot_projection _ p
  rw [oneTilt,grow, show 1-twist U (cutM s)=twist U (1-cutM s) from (by rw [map_sub,map_one]),
    ← map_sub,← map_smul,←breeze_exp]
  have h (x : ℝ) (P : Op I) : x • twist U P = twist U (x • P) := (map_smul ..).symm
  rw [h,h,←map_add]
  congr 1
  let f (i : I) : ℝ := if i∈s then -t else t
  rw [show t • ((1:Op I) - cutM s - cutM s) = Matrix.diagonal (fun i => (f i : ℂ)) from ?_, phase_diag]
  all_goals ext i j; by_cases v:i=j
  all_goals first | simp [f,v, cutM]; done | (subst j; by_cases t : i ∈ s <;> simp [f,t,cutM])

lemma oneTilt_self (p : IsStarProjection P) (t : ℝ) : IsSelfAdjoint (oneTilt P t) := by
  rw [oneTilt_price p]
  exact ((IsSelfAdjoint.all _).smul p.isSelfAdjoint).add
    ((IsSelfAdjoint.all _).smul p.one_sub.isSelfAdjoint)

lemma oneTilt_inverse (P : Op I) (t : ℝ) : oneTilt P t * oneTilt P (-t) = 1 := by
  rw [oneTilt,oneTilt,grow,grow,neg_smul,wind_inv]

lemma left_project (p : IsStarProjection P) (t : ℝ) : oneTilt P t * P = Real.exp (-t) • P := by
  rw [oneTilt_price p, add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,sub_mul,one_mul,
    p.isIdempotentElem.eq,sub_self, smul_zero, add_zero]

/-- We need only a constant bound (could be sharpened). -/
lemma oneTilt_cap (p : IsStarProjection P) (t : ℝ) : ‖oneTilt P t‖ ≤ 2 * Real.exp |t| := by
  have u (a : ℝ) (x : Op I) (q : IsStarProjection x) :
      ‖Real.exp a • x‖ ≤ Real.exp a := by
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (q.norm_le _)
  rw [oneTilt_price p, two_mul]
  exact (norm_add_le ..).trans (add_le_add ((u _ _ p).trans
    (Real.exp_monotone (neg_le_abs _))) ((u _ _ p.one_sub).trans (Real.exp_monotone (le_abs_self _))))

theorem realScalarActs {J : Type*} [Fintype J] [DecidableEq J] (c : ℝ) (P : Op J) (x : Ket J) :
    acts (c • P) x = c • acts P x := by rw [← Complex.coe_smul, ← Complex.coe_smul c (acts P x), act_smul]

theorem sea_scalar_cost (p : IsStarProjection P) (x : Wave I) (h : Sea P x) (t : ℝ) :
    acts (quant (Real.exp t • (1 : Op I))) x = Real.exp (t*P.trace.re) • x := by
  let V := Real.exp t • (1 : Op I)
  suffices e : quant V * lineOp P = Real.exp (t*P.trace.re) • lineOp P by
    change acts (quant V) _ = _
    nth_rw 1 [← h.1]
    rw [←act_mul,e,realScalarActs,h.1]
  obtain ⟨U,s,rfl⟩ := spot_projection _ p
  rw [line_twist,trace_twist]
  have hz : twist (quantU U) (quant V) = quant V := by rw [← quant_twist]; unfold V; rw [map_smul,map_one]
  nth_rw 1 [←hz]; rw [←map_mul,←map_smul]
  apply congrArg
  rw [cutLine,trace_cut]
  have hV : V = Matrix.diagonal fun _ : I => ((Real.exp t : ℝ) : ℂ) := by unfold V; ext i j; by_cases h:i=j <;> simp [h]
  rw [hV,quant_diag]; ext i j; by_cases a:i=j
  · subst j; by_cases b:i=s
    · subst i; rw [cutM,Matrix.diagonal_mul_diagonal]; simp [mul_comm (↑t : ℂ), Complex.exp_nat_mul]
    simp [cutM,Matrix.mul_diagonal,b]
  simp [cutM,Matrix.mul_diagonal,a]

-- the one-particle maps, in particular the normalizing shear limit, won't mix degrees
theorem quant_scaled (p : IsStarProjection P) (x : Wave I) (h : Sea P x) (R : Op I) (t : ℝ) :
    acts (quant (Real.exp t • R)) x = Real.exp (t*P.trace.re) • acts (quant R) x := by
  rw [show Real.exp t • R = R * (Real.exp t • (1 : Op I)) by rw [Algebra.mul_smul_comm,mul_one],
    quant_mul,act_mul,sea_scalar_cost p x h,(acts (quant R)).map_smul_of_tower]

lemma wholeTilt_self (p : IsStarProjection P) (t : ℝ) : IsSelfAdjoint (wholeTilt P t) := by
  have h := oneTilt_self p t; rw [tilt_spec p]
  exact (IsSelfAdjoint.all _).smul (show IsSelfAdjoint (quant (oneTilt P t)) from (quant_star ..).symm.trans (congr_arg quant h.star_eq))

lemma wholeTilt_inv (P : Op I) (t : ℝ) : wholeTilt P t * wholeTilt P (-t)=1 := by
  unfold wholeTilt; rw [neg_smul,wind_inv]

lemma stays (p : IsStarProjection P) (R : Op I) (hp : R * P = P) (x : Wave I) (h : Sea P x) :
    acts (quant R) x=x := by
  have he : acts (quant P) x=x := by nth_rw 1 [←h.1]; rw [←act_mul,line_quant p,h.1]
  nth_rw 1 [←he]; rw [←act_mul,←quant_mul,hp,he]

theorem wholeTilt_stays (p : IsStarProjection P) (x : Wave I) (h : Sea P x) (t : ℝ) :
    acts (wholeTilt P t) x=x := by
  rw [tilt_spec p,realScalarActs,←quant_scaled p x h]
  apply stays p _ _ x h
  rw [Algebra.smul_mul_assoc,left_project p,smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]

#print axioms wholeTilt_stays

end YM.CF.WakeInvestment
