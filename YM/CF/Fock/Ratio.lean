import YM.CF.Fock.Switchboard

/-! Frame-independent square ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
section
variable {n : Type*} [DecidableEq n] [Fintype n]

def relay (P A C : Op n) := body P C * (stage P A)⁻¹+(1-P)
lemma stage_il {P A : Op n} (h : IsStarProjection P) (g : IsUnit (stage P A)) :
    cc P*(stage P A)⁻¹=(stage P A)⁻¹*P := by
  let E := stage P A
  have H := stage_left h A; rw [←stage_right h] at H
  change P*E=E*cc P at H
  change cc P*E⁻¹=E⁻¹*P
  calc _ = E⁻¹ * (E*cc P) * E⁻¹ := by rw [←mul_assoc,(live (show IsUnit E from g)).2,one_mul]
       _ = _ := by rw [←H,mul_assoc,mul_assoc,(live (show IsUnit E from g)).1,mul_one]
lemma relay_lines {P A : Op n} (h : IsStarProjection P) (g : IsUnit (stage P A)) (C : Op n) :
    relay P A C * P=body P C*(stage P A)⁻¹ ∧ P*relay P A C=body P C*(stage P A)⁻¹ := by
  unfold relay; rw [add_mul,mul_assoc,←stage_il h g,←mul_assoc,body_right h,mul_add, ←mul_assoc P,body_left h,Porth h,sub_mul,one_mul,h.isIdempotentElem,sub_self,add_zero]; exact ⟨rfl,rfl⟩
lemma relay_base {P A : Op n} (h : IsStarProjection P) (g : IsUnit (stage P A)) : relay P A A=1 := by
  rw [relay,show body P A*(stage P A)⁻¹=P by
    nth_rw 1 [← stage_left h A]; rw [mul_assoc,(live g).1,mul_one],add_sub_cancel]
lemma relay_carry {P A : Op n} (h : IsStarProjection P) (g : IsUnit (stage P A)) (C : Op n) :
    relay P A C * (body P A+(1-P)) = body P C+(1-P) := by
  rw [mul_add,show relay P A C*(1-P) = 1-P by rw [mul_sub,mul_one,(relay_lines h g C).1,relay,add_sub_cancel_left]]
  congr 1
  rw [←stage_left h A,←mul_assoc,(relay_lines h g C).1, mul_assoc,(live g).2,mul_one]
  -- WARNING padding outside P multiplication with 1-P only; holds even if A bar basis cc P 
lemma relay_twist {P A : Op n} (g : IsUnit (stage P A)) (C : Op n) (U : UNI n) :
    relay (twist U P) (congrC U A) (congrC U C)=twist U (relay P A C) := by
  unfold relay; rw [stage_twist,board_twist,inv_twC _ g,map_add,map_mul,map_sub,map_one,← map_mul,congr_form,twist_formula]
  congr 1; let V := ccU U
  simp only [←mul_assoc]; rw [mul_assoc (U.val*body P C),show star _ * (ccU U).val=1 from V.property.1,mul_one]
  rw [twist_formula]; simp only [←mul_assoc]
lemma switch_cont {X : Type*} [TopologicalSpace X] (b e f : X→Op n) {x : X} (h : ContinuousAt b x) (g : ContinuousAt e x) (k : ContinuousAt f x) (p : IsUnit (e x)) : ContinuousAt (fun t=> b t * (e t)⁻¹+f t) x := by
  let J := fun A : Op n=>A⁻¹; change ContinuousAt (b*(J ∘ e)+f) x
  exact (h.mul ((show ContinuousAt J (e x) from InvC_cont (A:=e x) p).comp g)).add k
lemma relay_contAt {P A C : Op n} (g : IsUnit (stage P A)) :
    ContinuousAt (fun t : Op n × Op n × Op n => relay t.1 t.2.1 t.2.2) (P,A,C) := by
  let b := fun t : Op n×Op n×Op n=>stage t.1 t.2.1
  let x := fun t : Op n × Op n × Op n => body t.1 t.2.2
  let v := fun t : Op n × Op n × Op n => 1-t.1
  have hb : Continuous b := by unfold b stage body; fun_prop
  have Hx : Continuous x := by unfold x body; fun_prop
  have Hv : Continuous v := by unfold v; fun_prop
  exact switch_cont x b v Hx.continuousAt hb.continuousAt Hv.continuousAt g
lemma relay_gap {P A C : Op n} (h : IsStarProjection P) (g : IsUnit (stage P A)) (he : ‖(stage P A)⁻¹‖ ≤ 2) :
    ‖relay P A C-1‖ ≤ ‖C-A‖*2 := by
  nth_rw 1 [← relay_base h g]; unfold relay; rw [add_sub_add_right_eq_sub,←sub_mul,show body P C-body P A= P*(C-A)*cc P by rw [body,body,mul_sub,sub_mul]]
  have hp := IsStarProjection.norm_le P h
  apply (norm_mul_le ..).trans (mul_le_mul _ he (norm_nonneg _) (norm_nonneg _))
  apply (norm_mul_le ..).trans
  apply (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))) ((ccProj h).norm_le _) (norm_nonneg _) (by positivity)).trans
  simp
end
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma pf_ratio {A C : Op n} (s : Finset n) (h : Aᵀ= -A) (g : Cᵀ= -C) (k : IsUnit (stage (cutM s) A)) :
    pf C s^2=(relay (cutM s) A C).det*pf A s^2 := by
  rw [pf_square _ C g,pf_square _ A h,principal,principal,← Matrix.det_mul]
  congr 1; rw [padded,padded]
  simpa only [body,cut_real] using (relay_carry (P:=cutM s) (cutM_idp _) k C).symm
lemma det_twist (U : UNI n) (A : Op n) : (twist U A).det=A.det := by
  rw [twist_formula,Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,show U.val * star U.val=1 from U.property.2,Matrix.det_one,one_mul]
def stratum (U : UNI n) (s : Finset n) (A : Op n) := inner ℂ (wedge U.val s) (pairWave A)
lemma stratum_pf (U : UNI n) (s : Finset n) (A : Op n) : stratum U s A=pf (congrC (star U) A) s := by
  rw [stratum,pf,congrC,←pair_cov]; change _=(acts (quant (star U.val)) _).ofLp _
  rw [←basis_inner,←act_inner,quant_star,star_star,quant_column]
lemma strata {A C : Op n} (U : UNI n) (s : Finset n) (h : Aᵀ= -A) (g : Cᵀ= -C)
    (k : IsUnit (stage (twist U (cutM s)) A)) :
    stratum U s C^2=(relay (twist U (cutM s)) A C).det*stratum U s A^2 := by
  let V : UNI n := star U
  have hk := live_cong V k; rw [← stage_twist V, twist_inv] at hk
  rw [←det_twist V,←relay_twist k,show twist V (twist U (cutM s))=cutM s from twist_inv ..,stratum_pf,stratum_pf]
  exact pf_ratio s (skew_form h) (skew_form g) hk
lemma placed (U : UNI n) (s : Finset n) (A : Op n) : filled (twist U (cutM s)) A=stratum U s A • wedge U.val s := act_twistLine ..
lemma strata_gap (U : UNI n) (s : Finset n) (A : Op n) (he : filled (twist U (cutM s)) A≠0) : stratum U s A≠0 := by
  intro h; apply he; rw [placed,h,zero_smul]
end YM.CF.Fock
