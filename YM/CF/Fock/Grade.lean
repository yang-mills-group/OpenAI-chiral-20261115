import YM.CF.Fock.Quant

/-! Grading-preserving identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
section helpers
variable {n : Type*} [DecidableEq n] [Fintype n]
lemma diag_apply (f : n → ℂ) (x : Ket n) (i : n) :
    (acts (Matrix.diagonal f) x).ofLp i=f i*x.ofLp i := by rw [act_at]; simp [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul]
lemma diag_basis (f : n → ℂ) (i : n) :
    acts (Matrix.diagonal f) (basisKet i)=f i • basisKet i := by
  apply PiLp.ext; intro j; rw [diag_apply]; by_cases h:j=i <;> simp [h,Pi.single_apply]
end helpers
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma quant_diag (f : n → ℂ) :
    quant (Matrix.diagonal f)=Matrix.diagonal fun s => ∏ i∈s, f i := by
  apply op_scale_column; intro s; rw [quant_column]
  induction s using Finset.induction_on with
  | empty => rw [wedge_empty,prod_empty,one_smul]
  | @insert i s e ih =>
    rw [wedge_any _ _ _ e,ih,diag_basis,map_smul,map_smul,create_put,act_smul,put_act,if_neg e,prod_insert e]
    simp only [smul_smul]
    congr 1
    calc
      _ = (parity i s * parity i s)*(f i * ∏ j∈s, f j) := by ac_rfl
      _ = _ := by simp
/-- Coordinate projection. -/
def cutM {I : Type*} [DecidableEq I] (s : Finset I) : Op I := Matrix.diagonal fun i => if i∈s then 1 else 0
lemma cutM_idp {I : Type*} [DecidableEq I] [Fintype I] (s : Finset I) : IsStarProjection (cutM s) := by
  constructor
  · unfold IsIdempotentElem; rw [cutM,Matrix.diagonal_mul_diagonal]; ext i j; by_cases h:i=j
    · subst j; by_cases g:i∈s <;> simp [g]
    simp [h]
  unfold IsSelfAdjoint; ext i j; by_cases h:i=j
  · subst j; by_cases g:i∈s <;> simp [cutM,g]
  · simp [cutM,h,Ne.symm h]
lemma quantCut (s : Finset n) : quant (cutM s)=cutM s.powerset := by
  rw [cutM,quant_diag]; unfold cutM; congr 1; funext t; by_cases e:t ⊆ s
  · rw [if_pos (mem_powerset.mpr e),prod_eq_one]; exact fun i hi => if_pos (e hi)
  rw [if_neg (by simpa)]; obtain ⟨i,h,g⟩ := not_subset.mp e; exact prod_eq_zero h (if_neg g)
lemma quant_grade (A : Op n) (s t : Finset n) (h : s.card≠t.card) : quant A s t=0 := by
  let f := fun _ : n => (2:ℂ)
  have he : Matrix.diagonal f=(2:ℂ) • (1 : Op n) := by ext i j; by_cases h : i=j <;> simp [h,f]
  have hk : Matrix.diagonal f * A=A*Matrix.diagonal f := by rw [he,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,one_mul]
  have hg := congrArg quant hk; simp only [quant_mul,quant_diag,prod_const,f] at hg
  have hb := Matrix.ext_iff.mpr hg s t; rw [Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm _ ((2:ℂ)^_)] at hb
  by_contra hx
  have hm := mul_right_cancel₀ hx hb
  have hq : (2:ℕ)^s.card=(2:ℕ)^t.card := by exact_mod_cast hm
  exact h ((pow_right_strictMono₀ (show 1 < (2:ℕ) by norm_num)).injective hq)
def selector (n : Type*) [DecidableEq n] [Fintype n] (k : ℕ) : FC n := cutM (univ.filter fun s => s.card=k)
lemma selector_quant (k : ℕ) (A : Op n) : quant A*selector n k=selector n k*quant A := by
  ext s t; rw [selector,cutM,Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h:s.card=t.card
  · simp [h,mul_comm]
  simp [quant_grade A s t h]
lemma spot_projection (P : Op n) (h : IsStarProjection P) : ∃ U : UNI n, ∃ s, P=twist U (cutM s) := by
  obtain ⟨U,d,rfl⟩ := spectral_exists _ h.isSelfAdjoint
  let f : n → ℂ := fun i => (d i : ℂ)
  have hi : Matrix.diagonal f*Matrix.diagonal f=Matrix.diagonal f :=
    (twist U).injective (by rw [map_mul]; exact h.isIdempotentElem)
  rw [Matrix.diagonal_mul_diagonal] at hi
  let s := univ.filter fun i => f i=1
  refine ⟨U,s,?_⟩; unfold spectral
  apply congrArg; unfold cutM
  congr 1; funext i; change f i=_
  have he : f i * f i=f i := by simpa using Matrix.ext_iff.mpr hi i i
  by_cases e : f i=0 <;> simp [s,e]
  have ht : f i=1 := mul_left_cancel₀ e (by rw [mul_one]; exact he)
  simp [ht]
end YM.CF.Fock
