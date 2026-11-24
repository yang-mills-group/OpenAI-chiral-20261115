import YM.CF.Fock.PfMinor

/-! Partial alternating compression and its gapped complement. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [DecidableEq n] [Fintype n]

def body (P C : Op n) := P*C*cc P
def stage (P C : Op n) := body P C+body (1-P) C
lemma ccProj {P : Op n} (h : IsStarProjection P) : IsStarProjection (cc P) := by
  constructor
  · unfold IsIdempotentElem; rw [←cc_mul,h.isIdempotentElem]
  unfold IsSelfAdjoint; rw [←cc_star, h.isSelfAdjoint]
lemma Porth {P : Op n} (h : IsStarProjection P) : P*(1-P)=0 := by rw [mul_sub,mul_one,h.isIdempotentElem,sub_self]
lemma body_left {P : Op n} (h : IsStarProjection P) (C : Op n) : P*body P C=body P C := by
  unfold body; rw [←mul_assoc,←mul_assoc,h.isIdempotentElem]
lemma body_right {P : Op n} (h : IsStarProjection P) (C : Op n) : body P C*cc P=body P C := by
  unfold body; rw [mul_assoc,show cc P*cc P=cc P from (ccProj h).isIdempotentElem]
lemma stage_left {P : Op n} (h : IsStarProjection P) (C : Op n) : P*stage P C=body P C := by rw [stage,mul_add,body_left h,←body_left h.one_sub,←mul_assoc,Porth h,zero_mul,add_zero]
lemma stage_right {P : Op n} (h : IsStarProjection P) (C : Op n) : stage P C *cc P=body P C := by
  rw [stage,add_mul,body_right h,←body_right h.one_sub, mul_assoc]
  have hi : cc (1-P)*cc P=0 := by rw [←cc_mul,sub_mul,one_mul,h.isIdempotentElem,sub_self,cc_zero]
  rw [hi,mul_zero,add_zero]
lemma board_twist (U : UNI n) (P C : Op n) : body (twist U P) (congrC U C)=congrC U (body P C) := by
  unfold body; rw [congr_form,congr_form,cc_twist]
  let V := ccU U; rw [twist_formula V (cc P)]
  have hi : star V.val*V.val=1 := V.property.1
  simp only [←mul_assoc, twist_product]
  change U.val*P*C*star V.val*V.val*cc P*star V.val=_; rw [mul_assoc (U.val*P*C), hi, mul_one]
lemma stage_twist (U : UNI n) (P C : Op n) : stage (twist U P) (congrC U C)=congrC U (stage P C) := by
  unfold stage; rw [board_twist,show 1 - twist U P=twist U (1-P) by rw [map_sub,map_one],board_twist]; simp only [congrC,mul_add,add_mul]
@[fun_prop] lemma cc_cont : Continuous (cc (n:=n)) := by refine continuous_matrix ?_; intro i j; exact (continuous_id.matrix_elem i j).star -- name collision
@[fun_prop] lemma body_cont : Continuous (fun u : Op n×Op n=>body u.1 u.2) := by unfold body; fun_prop
@[fun_prop] lemma stage_cont : Continuous (fun u : Op n×Op n=>stage u.1 u.2) := by unfold stage body; fun_prop
lemma live {A : Op n} (h : IsUnit A) : A * A⁻¹=1 ∧ A⁻¹ * A=1 := by
  rw [Matrix.isUnit_iff_isUnit_det] at h
  exact ⟨Matrix.mul_nonsing_inv _ h,Matrix.nonsing_inv_mul _ h⟩
lemma live_of {A S : Op n} (h : A*S=1) : IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr; rw [isUnit_iff_ne_zero]; apply left_ne_zero_of_mul
  rw [← Matrix.det_mul A S,h,Matrix.det_one]; exact one_ne_zero
lemma starU (U : UNI n) : IsUnit U.val := live_of (show U.val*star U.val=1 from U.property.2)
lemma live_cong (U : UNI n) {C : Op n} (h : IsUnit C) : IsUnit (congrC U C) := by
  rw [congr_form]; exact ((starU U).mul h).mul (starU (n:=n) (star (ccU U)))
lemma InvC_cont {A : Op n} (h : IsUnit A) : ContinuousAt (fun t : Op n=> t⁻¹) A := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]
  have h1 : Continuous fun x : Op n=>x.det := continuous_id.matrix_det
  have h2 : Continuous fun x : Op n=>x.adjugate := continuous_id.matrix_adjugate
  exact (h1.continuousAt.inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp h))).smul h2.continuousAt
lemma inv_twC (U : UNI n) {A : Op n} (h : IsUnit A) : (congrC U A)⁻¹=(ccU U).val*A⁻¹ * star U.val := by
  let C := congrC U A; let Q := ccU U
  have he : C * (Q.val*A⁻¹*star U.val) =1 := by
    have ht : C*Q.val=U.val*A := congr_product ..
    rw [←mul_assoc C, ←mul_assoc C,ht,mul_assoc U.val A,(live h).1,mul_one]; exact U.property.2
  rw [← one_mul (_ * star U.val),← (live (live_cong U h)).2,mul_assoc,he,mul_one]
lemma nearOne {A : Op n} (e : ‖1-A‖ < 1) : IsUnit A := ⟨Units.oneSub _ e, by rw [Units.val_oneSub, sub_sub_cancel]⟩
lemma projPhase {P : Op n} (h : IsStarProjection P) : cc P-cc (1-P)∈ unitary (Op n) := by
  let p := cc P; let q := cc (1-P); have hp : IsStarProjection p := ccProj h; have he : q=1-p := by simp [q,p]
  have hq : IsStarProjection q := ccProj h.one_sub
  have hu : p*q=0 := by rw [he,Porth hp]
  have hz : q*p=0 := by rw [he,sub_mul,one_mul,hp.isIdempotentElem,sub_self]
  change p-q∈ _
  have hk : (p-q)*(p-q)=1 := by rw [mul_sub,sub_mul,sub_mul,hp.isIdempotentElem,hq.isIdempotentElem,hu,hz,he]; abel
  constructor <;> rwa [star_sub,hp.isSelfAdjoint,hq.isSelfAdjoint]
lemma stage_gap [Nonempty n] {P : Op n} (h : IsStarProjection P) (C : Op n) :
    ‖stage P C-C‖ = ‖P*C-C*cc P‖ := by
  have he : stage P C-C=(P*C-C*cc P)*(cc P-cc (1-P)) := by
    -- multiply right ccP: side E-C =P C ccP-C ccP matches (PC-CccP)ccP yes
    rw [stage,body,body,cc_sub,cc_one]
    simp only [mul_sub,sub_mul,one_mul,mul_one, mul_assoc C (cc P), show cc P*cc P=cc P from (ccProj h).isIdempotentElem]
    abel -- tune sign!
  rw [he]; exact CStarRing.norm_mul_coe_unitary _ ⟨_,projPhase h⟩
lemma closeUnit [Nonempty n] {A : Op n} (U : UNI n) (g : ‖A-U.val‖<1) : IsUnit A := by
  let X := A*star U.val
  have he : ‖1-X‖=‖A-U.val‖ := by
    unfold X; rw [norm_sub_rev,←show U.val*star U.val=1 from U.property.2,←sub_mul]; exact CStarRing.norm_mul_coe_unitary _ (star U)
  have hx : IsUnit X := nearOne (he.trans_lt g)
  have hi : X*U.val=A := by unfold X; rw [mul_assoc,show star U.val*U.val=1 from U.property.1,mul_one]
  rw [←hi]; exact hx.mul (starU U)
lemma inv_close_le [Nonempty n] {A : Op n} (U : UNI n) (h : ‖A-U.val‖≤1/3) : IsUnit A ∧ ‖A⁻¹‖≤2 := by
  have H := closeUnit U (lt_of_le_of_lt h (by norm_num)); refine ⟨H,?_⟩
  have he : ‖A⁻¹‖ ≤ 1+‖U.val-A‖*‖A⁻¹‖ := by
    calc ‖A⁻¹‖ = ‖U.val*A⁻¹‖ := (CStarRing.norm_coe_unitary_mul U _).symm
         _ = ‖(1:Op n)+(U.val-A)*A⁻¹‖ := by rw [sub_mul,(live H).1,add_sub_cancel]
         _ ≤ _ := (norm_add_le ..).trans (add_le_add (by simp) (norm_mul_le ..))
  rw [norm_sub_rev] at he; nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg A⁻¹)]
end YM.CF.Fock
