import YM.CF.Thera.Hang
-- S tilt basis change and excitation grader
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 50000
noncomputable section
namespace YM.CF.Fock.Flux
open Function NormedSpace Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P E A B T L: Op I}
-- commutant band and shear. orientation matrix proofs will use these on one Spin block
structure Valve (P E A B:Op I) : Prop where
 live : A * B =1
 rest : B * A=1
 carry : A*P=P
 bring : B*P=P
 home : P*star B*E=star B*E
abbrev scarH (P E:Op I)(d:ℝ):Op I:= d⁻¹ • (P*E*(1-P))
lemma scar_forms (h:IsStarProjection P)(k:IsStarProjection E)(d:ℝ)(u:0<d)
 (e:E*P*E=d • E) : let S:=scarH P E d; Valve P E (1+S) (1-S):=by
 intro S; let y:ℝ:=d⁻¹; let Q:=1-P; have ht:Q*P=0:=by unfold Q; rw [sub_mul,one_mul,h.isIdempotentElem.eq,sub_self]
 have hP:P*Q=0:=by unfold Q; rw [mul_sub,mul_one,h.isIdempotentElem.eq,sub_self]
 have he:S*P=0:=by change (y • (P*E*Q))*P=0; rw [Matrix.smul_mul,mul_assoc,ht,mul_zero,smul_zero]
 have hf : S*S=0:=by nth_rw 2 [show S=y • (P*E*Q) from rfl]; rw [Matrix.mul_smul,← mul_assoc,← mul_assoc S P E, he,zero_mul,zero_mul,smul_zero]
 constructor
 · simp only [add_mul,mul_sub,one_mul,mul_one,hf]; abel
 · simp only [sub_mul,mul_add,mul_one,one_mul,hf]; abel
 · rw [add_mul,one_mul,he,add_zero]
 · rw [sub_mul,one_mul,he,sub_zero]
 have hv:star S=y • (Q*(E*P)):=by
    change star (y • (P*E*Q))=_; simp only [star_smul,star_mul,star_trivial, k.isSelfAdjoint.star_eq, h.isSelfAdjoint.star_eq, show star Q=Q from h.one_sub.isSelfAdjoint.star_eq]
 have hz:P*star S=0:=by rw [hv,Matrix.mul_smul,← mul_assoc,hP,zero_mul,smul_zero]
 have hl: star S*E=Q*E:=by rw [hv,Matrix.smul_mul,mul_assoc Q,e,Matrix.mul_smul, inv_smul_smul₀ u.ne'] -- Matrix formula scope
 rw [star_sub,star_one,mul_sub P,mul_one,hz,sub_zero,sub_mul,one_mul,hl]; unfold Q; rw [sub_mul,one_mul,sub_sub_cancel]
variable {d:ℝ}
lemma scar_norm (h:IsStarProjection P)(k:IsStarProjection E)(u:0<d)(e:E*P*E=d • E) : Real.sqrt d* ‖scarH P E d‖ ≤ 1:=by
 have hp: ‖P*E‖^2≤d:=by
    rw [sq, ← CStarRing.norm_star_mul_self, star_mul,h.isSelfAdjoint,k.isSelfAdjoint,←mul_assoc (E*P), mul_assoc E P, h.isIdempotentElem.eq,e,norm_smul,Real.norm_of_nonneg u.le]
    exact mul_le_of_le_one_right u.le (k.norm_le _)
 have he: ‖P*E‖≤Real.sqrt d:=by apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1; rw [Real.sq_sqrt u.le]; exact hp
 unfold scarH; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr u).le]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (h.one_sub.norm_le _)).trans he)) (inv_pos.mpr u).le) (Real.sqrt_nonneg _)) (le_of_eq ?_)
 rw [mul_left_comm,←sq,Real.sq_sqrt u.le, inv_mul_cancel₀ u.ne']

-- V_b
abbrev chips (P:Op I)(b:ℝ):Op I:= (Real.exp (-b)) • P + Real.exp b • (1-P)
lemma chips_act (b:ℝ)(h:IsStarProjection P): chips P b*P=(Real.exp (-b)) • P:=by unfold chips; rw [add_mul,Matrix.smul_mul,Matrix.smul_mul,sub_mul,h.isIdempotentElem.eq,one_mul,sub_self,smul_zero,add_zero]
lemma chips_base (b:ℝ)(h:IsStarProjection P): P*chips P b=(Real.exp (-b)) • P:=by unfold chips; rw [mul_add,Matrix.mul_smul,Matrix.mul_smul,mul_sub,h.isIdempotentElem.eq,mul_one,sub_self,smul_zero,add_zero]
lemma chips_top (b:ℝ)(h:IsStarProjection P): chips P b*(1-P)=(Real.exp b) • (1-P):=by rw [mul_sub,mul_one,chips_act _ h]; unfold chips; abel
lemma chips_flip (b:ℝ)(h:IsStarProjection P):star (chips P b)=chips P b:= by unfold chips; rw [star_add,star_smul,star_smul,show star P=P from h.2,show star (1-P)=1-P from h.one_sub.isSelfAdjoint,star_trivial,star_trivial]
lemma chips_ps (a b:ℝ)(h:IsStarProjection P): chips P a*chips P b= chips P (a+b):=by
 rw [show chips P b= _ • _ + _ from rfl,mul_add,Matrix.mul_smul,Matrix.mul_smul,chips_act _ h,chips_top _ h, smul_smul,smul_smul]; unfold chips; rw [Real.exp_add,neg_add, Real.exp_add]; simp [mul_comm]
lemma chips_zero (P:Op I): chips P 0=1:=by simp [chips]
-- Heat equality constructive, scalar explicit for P. One notion of energy in all grading estimates.
abbrev rband (P:Op I):ℝ:= P.trace.re
abbrev excite (P:Op I):FC I:= rband P • (1:FC I)+ dg (1-(2:ℝ) • P)
abbrev knight (P:Op I)(b:ℝ):= Real.exp (b*rband P) • quant (chips P b)
lemma knight_star (h:IsStarProjection P)(b:ℝ): star (knight P b)=knight P b:=by unfold knight; rw [star_smul, ←quant_star, chips_flip _ h,star_trivial]
lemma knight_seg (h:IsStarProjection P)(a b:ℝ): knight P a * knight P b=knight P (a+b):=by unfold knight; rw [Matrix.smul_mul,Matrix.mul_smul, smul_smul,←quant_mul,chips_ps _ _ h,add_mul,Real.exp_add]
lemma knight_start (P:Op I): knight P 0=1:=by rw [knight,chips_zero,quant_one,zero_mul,Real.exp_zero,one_smul]
lemma rband_count (U:UNI I)(s:Finset I): rband (twist U (cutM s))=s.card:=by unfold rband; rw [trace_twist,trace_cut]; norm_cast
lemma chips_twist (U:UNI I)(A:Op I)(b:ℝ): twist U (chips A b)= chips (twist U A) b:=by simp only [chips,map_smul,map_add,map_sub,map_one]
lemma knight_twist (U:UNI I)(A:Op I)(b:ℝ): twist (quantU U) (knight A b)=knight (twist U A) b:=by simp only [knight,map_smul,rband,trace_twist,←chips_twist,quant_twist]
lemma excite_star (P:Op I)(h:IsStarProjection P): star (excite P)=excite P:= by
 unfold excite; simp only [star_add,star_smul,star_one,←dg_star,star_sub,star_trivial,h.isSelfAdjoint.star_eq]
lemma excite_turn (U:UNI I)(A:Op I): twist (quantU U) (excite A) = excite (twist U A):=by unfold excite rband; rw [map_add,map_smul,dg_cov,map_sub,map_one,map_one,trace_twist,map_smul] -- tune

def hole (s t:Finset I):ℝ:= (s.card:ℝ)+∑ i∈ t, if i∈s then (-1:ℝ) else 1
lemma hole_diag (s:Finset I): hole s s=0:=by unfold hole; rw [sum_congr rfl (g:=fun _=>-1) (fun i u=>if_pos u),sum_const,nsmul_eq_mul]; ring
lemma k_val (b:ℝ)(s:Finset I) : chips (cutM s) b=Matrix.diagonal fun i:I=> if i∈s then ((Real.exp (-b):ℝ):ℂ) else ↑(Real.exp b):=by
 ext i j; by_cases h:i=j; swap; · simp [chips,cutM,h]
 subst i
 by_cases k:j∈s <;> simp [chips,cutM,k]
lemma k_Earn (b:ℝ)(s:Finset I): knight (cutM s) b=Matrix.diagonal fun t:Finset I=> ((Real.exp (b*hole s t):ℝ):ℂ):=by
 rw [knight,k_val,quant_diag,rband,trace_cut,Complex.natCast_re]; ext i j; by_cases p:i=j; swap; · simp [p,Matrix.diagonal_apply]
 subst j; rw [Matrix.smul_apply,Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq,←Complex.coe_smul,smul_eq_mul,hole,mul_add,Real.exp_add,Complex.ofReal_mul]; congr 1; rw [mul_sum,Real.exp_sum,Complex.ofReal_prod]; apply prod_congr rfl; intro k h; by_cases l:k∈s <;> simp [l]
lemma k_Excite (s:Finset I): excite (cutM s) = Matrix.diagonal fun t:Finset I=> ((hole s t:ℝ):ℂ):=by
 rw [excite,rband,trace_cut,Complex.natCast_re,show 1-(2:ℝ) • cutM s= Matrix.diagonal fun i:I=> if i∈s then (-1:ℂ) else 1 from ?_,dg_diag]
 · ext i j; by_cases h:i=j
   swap; · simp [h,Matrix.one_apply]
   subst j; unfold hole; rw [Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq,Matrix.one_apply_eq,Complex.ofReal_add,Complex.ofReal_sum]; congr 1; · simp
   apply sum_congr rfl; intro k p; by_cases hk:k∈s <;> simp [hk]
 ext i j; by_cases h:i=j; swap; · simp [cutM,Matrix.one_apply,h]
 subst j; by_cases k:i∈s <;> simp [cutM,←Complex.coe_smul,k, Complex.ofReal_ofNat] <;> norm_num
lemma k_card (h:IsStarProjection P)(b:ℝ): NormedSpace.exp (b • excite P)= knight P b:=by
 obtain ⟨U,s,rfl⟩:= spot_projection P h
 rw [← knight_twist, ← excite_turn,← map_smul (twist (quantU U)) b,← breeze_exp, k_Excite,k_Earn] -- tune
 congr 1
 rw [←Matrix.diagonal_smul,phase_diag]; apply congrArg; ext i; change Complex.exp (b • ((hole s i:ℝ):ℂ))=_
 rw [←Complex.coe_smul, smul_eq_mul, ←Complex.ofReal_mul, ←Complex.ofReal_exp]
set_option maxHeartbeats 40000 in
lemma knight_hold (h:IsStarProjection P)(b:ℝ)(u:Wave I)(p:Sea P u): acts (knight P b) u=u:=by
 obtain ⟨U,s,rfl⟩:= spot_projection P h; rw [← knight_twist]; let A:=cutM s; let W:=wedge U.val s; have he:u= inner ℂ W u • W:= p.1.symm.trans (act_twistLine ..)
 let t:=inner ℂ W u; let V:=twist (quantU U) (knight (cutM s) b)
 have hv: W=acts (quantU U).val (basisKet s):=(quant_column ..).symm
 have hs:acts (knight (cutM s) b) (basisKet s)=basisKet s:=by rw [k_Earn,diag_basis,hole_diag,mul_zero,Real.exp_zero,Complex.ofReal_one, one_smul]
 have hx:acts V W=W:=hv ▸ (swivel (quantU U) (knight (cutM s) b) (basisKet s)).symm.trans (congrArg (acts (quantU U).val) hs)
 exact (congrArg (acts V) he).trans ((map_smul (acts V) t W).trans ((congrArg (fun x:Wave I=> t • x) hx).trans he.symm))
-- cheaper first estimate before h
lemma chips_budget (b:ℝ)(B:ℝ)(u:|b|≤B)(h:IsStarProjection P): ‖chips P b‖ ≤ 2 * Real.exp B :=by
 unfold chips; refine (norm_add_le ..).trans ((add_le_add ?_ ?_).trans_eq (two_mul (Real.exp B)).symm)
 · rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _|>.le)]; exact mul_one (Real.exp B) ▸ mul_le_mul (Real.exp_monotone ((neg_le_abs b).trans u)) (h.norm_le _) (norm_nonneg _) (Real.exp_pos _).le
 rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _|>.le)]; exact mul_one (Real.exp B) ▸ mul_le_mul (Real.exp_monotone ((le_abs_self b).trans u)) (h.one_sub.norm_le _) (norm_nonneg _) (Real.exp_pos _).le
end YM.CF.Fock.Flux
end
