import YM.CF.Fock.Affine
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! Excitation coefficients with redundant hole/particle labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset NormedSpace
attribute [local instance] opCStarAlgebra
section core
variable {n : Type*} [Fintype n] [DecidableEq n] {P C : Op n}
-- shorten conjugation bookkeeping
lemma ccT (A : Op n) : (cc A)ᵀ=star A := by rw [cc, Matrix.transpose_transpose]
lemma reserve_cov (g : IsUnit (stage P C)) (U : UNI n) : reserve (twist U P) (congrC U C) = cc U.val * reserve P C * (cc U.val)ᵀ := by
  rw [reserve,stage_twist,inv_twC U g,twist_formula,ccT]; let K := ((ccU U).val*(stage P C)⁻¹)
  change K*_ * _=_; simp only [←mul_assoc]; rw [mul_assoc K,show star U.val * U.val=1 from U.property.1,mul_one]; unfold reserve; rw [←mul_assoc (cc U.val)]; rfl
lemma congr_mid (U : UNI n) (C S A : Op n) : congrC U C * (cc U.val * S * (cc U.val)ᵀ) * congrC U A=congrC U (C*S*A) := by
  rw [ccT]; let L := congrC U C
  simp only [←mul_assoc]; rw [show congrC U C * cc U.val=U.val*C from congr_product ..,congr_form _ A, congr_form]
  simp only [←mul_assoc]; rw [mul_assoc (U.val*C*S), show star U.val*U.val=1 from U.property.1,mul_one]
lemma drift_cov (g : IsUnit (stage P C)) (U : UNI n) : driftB (twist U P) (congrC U C)=cc U.val*driftB P C*U.valᵀ := by
  rw [driftB,driftB,reserve_cov g,ccT,show 1-twist U P=twist U (1-P) by rw [map_sub,map_one],cc_twist,twist_formula,congr_form,mul_neg, neg_mul,show U.valᵀ=star (ccU U).val by change _=star (cc U.val); rw [←cc_star,cc,star_star]]
  simp only [←mul_assoc]
  let S := cc U.val * reserve P C
  rw [mul_assoc S, show star U.val*U.val=1 from U.property.1,mul_one,mul_assoc (S*C), show star _*(ccU U).val=1 from (ccU U).property.1,mul_one]
lemma weld_cov (g : IsUnit (stage P C)) (U : UNI n) : weldB (twist U P) (congrC U C)=U.val*weldB P C*U.valᵀ := by
  change body (1-_) _=congrC U _; rw [reserve_cov g U,congr_mid, show 1-twist U P=twist U (1-P) by rw [map_sub,map_one],
    show congrC U C-congrC U (C*reserve P C*C)=congrC U (C-C*reserve P C*C) by unfold congrC; rw [mul_sub,sub_mul],board_twist]; rfl
end core

variable {n : Type*} [LinearOrder n] [Fintype n]
abbrev FN (n : Type*) := n → FC n
def dyad (A : Op n) (f g : FN n) := ∑ i, ∑ j, A i j • (f i*g j)
def prong (f : FN n) (S : Op n) (j : n) := ∑ i, S i j • f i
lemma dyad_prong (A S T : Op n) (f g : FN n) : dyad A (prong f S) (prong g T)=dyad (S*A*Tᵀ) f g := by
  unfold dyad prong; simp_rw [sum_mul,mul_sum,Matrix.mul_apply,sum_mul,sum_smul,smul_sum,
    Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,Matrix.transpose_apply]
  let D (i j p q : n) := (A i j*(T q j*S p i)) • (f p*g q)
  change ∑ i,∑ j,∑ p,∑ q, D i j p q=_
  simp_rw [sum_comm (f:=fun i j=>∑ p,∑ q,D i j p q), sum_comm (f:=fun i p=>∑ q,D i _ p q),
    sum_comm (f:=fun j p=>∑ i,∑ q,D i j p q), sum_comm (f:=fun i q=>D i _ _ q), sum_comm (f:=fun j q=>∑ i,D i j _ q)]
  simp [D,mul_comm,mul_assoc, mul_left_comm]
lemma dyad_twist (A : Op n) (U : UNI (Finset n)) (f g : FN n) : twist U (dyad A f g)=dyad A (fun i=> twist U (f i)) (fun i=>twist U (g i)) := by simp only [dyad,map_sum,twist_scalar,map_mul]
lemma dyad_plus (A B : Op n) (f g : FN n) : dyad (A+B) f g=dyad A f g+dyad B f g := by simp only [dyad,Matrix.add_apply,add_smul,sum_add_distrib]
lemma dyad_sub (A B : Op n) (f g : FN n) : dyad (A-B) f g=dyad A f g-dyad B f g := by simp only [dyad,Matrix.sub_apply,sub_smul,sum_sub_distrib]
lemma prong_t (S : Op n) (i : n) : prong takeF (cc S) i=remove (acts S (basisKet i)) := by rw [remove_def]; simp only [basis_act]; rfl
lemma prong_p (S : Op n) (i : n) : prong put S i=create (acts S (basisKet i)) := by rw [create_def]; simp only [basis_act]; rfl
lemma twist_t (U : UNI n) (i : n) : twist (quantU U) (takeF i) = prong takeF (cc U.val) i := by rw [←remove_take i,twist_remove,prong_t]
lemma twist_p (U : UNI n) (i : n) : twist (quantU U) (put i) = prong put U.val i := by rw [←create_put i,twist_create,prong_p]

def inning (f g : FN n) (D A W : Op n) := (2:ℂ)⁻¹ • (dyad D f f+dyad A f g-dyad Aᵀ g f+dyad W g g)
def excite (P C : Op n) := inning takeF put (reserve P C) (driftB P C) (weldB P C)
lemma inning_cov (f g : FN n) (D A W : Op n) (U : UNI (Finset n)) : twist U (inning f g D A W)=inning (fun i=>twist U (f i)) (fun i=>twist U (g i)) D A W := by simp only [inning,twist_scalar,map_add,map_sub,dyad_twist]
lemma inning_lift (f g : FN n) (D A W S T : Op n) :
    inning (prong f S) (prong g T) D A W=inning f g (S*D*Sᵀ) (S*A*Tᵀ) (T*W*Tᵀ) := by
  simp only [inning,dyad_prong, Matrix.transpose_mul, Matrix.transpose_transpose,mul_assoc]
lemma excite_cov {P C : Op n} (g : IsUnit (stage P C)) (U : UNI n) : twist (quantU U) (excite P C)=excite (twist U P) (congrC U C) := by
  simp only [excite,inning_cov,twist_t,twist_p,inning_lift,reserve_cov g,drift_cov g,weld_cov g]
lemma cub (s : Finset n) (f : FN n) : prong f (cutM s) = fun i=>if i∈s then f i else 0 := by
  funext i; unfold prong; rw [sum_eq_single i]; by_cases h:i∈s <;> simp [cutM,h]
  · intro j _ g; simp [cutM,g]
  simp
lemma dim_cut (s : Finset n) : cutM sᶜ=1-cutM s := by
  unfold cutM; ext i j; by_cases g:i=j
  · subst j; by_cases h:i∈s <;> simp [h]
  simp [g]
lemma drift_fits (s : Finset n) : prong (drift s) (cutM s)=prong takeF (cutM s) ∧ prong (drift s) (cutM sᶜ)=prong put (cutM sᶜ) := by
  constructor <;> (funext i; rw [cub,cub]; by_cases g:i∈s <;> simp [g,drift])
lemma crew {P C : Op n} (h : IsStarProjection P) (e : IsUnit (stage P C)) : cc P * reserve P C * (cc P)ᵀ=reserve P C ∧ cc P* driftB P C * (1-P)ᵀ=driftB P C ∧ (1-P)*weldB P C*(1-P)ᵀ=weldB P C := by
  have ho : cc (1-P)=(1-P)ᵀ := by rw [cc,h.one_sub.isSelfAdjoint]
  rw [ccT,h.isSelfAdjoint,reserve_l h e,reserve_r h,←ho]; refine ⟨rfl,?_,?_⟩
  · rw [driftB,mul_neg,neg_mul,←mul_assoc,←mul_assoc,reserve_l h e, mul_assoc (reserve _ _*_),show cc (1-P)*cc (1-P)=cc (1-P) from (ccProj h.one_sub).isIdempotentElem]
  change (1-P)*body (1-P) _*cc (1-P)=body (1-P) _; rw [body_left h.one_sub,body_right h.one_sub]
lemma dyad_drift {C : Op n} {s : Finset n} (g : IsUnit (stage (cutM s) C)) : inning (drift s) (drift s) (reserve (cutM s) C) (driftB (cutM s) C) (weldB (cutM s) C)=excite (cutM s) C := by
  let P := cutM s; let Q := cutM sᶜ; let D := reserve P C; let A := driftB P C; let W := weldB P C
  obtain ⟨h,e,b⟩ := crew (n:=n) (cutM_idp s) g; rw [cut_real] at h e; rw [←dim_cut s] at e b
  have H (f j : FN n) : inning (prong f P) (prong j Q) D A W=inning f j D A W := by
    rw [inning_lift,show P*D*Pᵀ=D from h,show P*A*Qᵀ=A from e, show Q*W*Qᵀ=W from b]
  change inning _ _ D A W=inning takeF put D A W; rw [←H (drift s) (drift s), ←H takeF put,show prong (drift s) P=prong takeF P from (drift_fits s).1,show prong (drift s) Q=prong put Q from (drift_fits s).2] -- tune
lemma flake_excite {s : Finset n} {C : Op n} (g : IsUnit (stage (cutM s) C)) : twist (flake s) (coupl (blend (cutM s) C))=excite (cutM s) C := by
  have h (A : Op n) : squareP A=dyad A put put := rfl
  rw [coupl,twist_scalar,h,dyad_twist]; simp_rw [flake_put]; rw [blend,dyad_plus,dyad_sub,dyad_plus]; exact dyad_drift g
-- expand creators already in desired sea sector
abbrev hideF (P : Op n) := prong takeF (cc P)
abbrev seekF (P : Op n) := prong put (1-P)
lemma in_sector {C P : Op n} (h : IsStarProjection P) (g : IsUnit (stage P C)) : inning (hideF P) (seekF P) (reserve P C) (driftB P C) (weldB P C)=excite P C := by
  rw [hideF,seekF,inning_lift,(crew h g).1,(crew h g).2.1,(crew h g).2.2]; rfl
end YM.CF.Fock
