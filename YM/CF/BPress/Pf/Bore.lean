import YM.CF.BPress.Pf.High
import YM.CF.BPress.Spin.Cellar
import YM.CF.Scroll.Loma
/-! Skew overlap, quantitative reserve, and relative determinant factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Scroll
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P C L A: Op I}{u:Wave I} {ε r:ℝ}
def toll (P C:Op I):=(1-P)*C*cc P
def cutC (P C:Op I):=P*C*cc P
def lost (P C:Op I):=P*C*(1-cc P)*star C*P
structure Bore (P C:Op I)(r:ℝ): Prop where
 p:IsStarProjection P
 unit:C∈unitary (Op I)
 sk:Cᵀ= -C
 low:‖toll P C‖≤r
 hi:r<1

lemma forest (U:UNI I)(C L:Op I): cutC (twist U L) (congrC U C) = congrC U (cutC L C):=board_twist ..
lemma toll_twist(U:UNI I)(A C:Op I): toll (twist U A) (congrC U C) = congrC U (toll A C):=by
 let V:=ccU U; unfold toll; rw [cc_twist, show 1-twist U A=twist U (1-A) by rw [map_sub,map_one], twist_formula,congr_form, twist_formula];
 simp only [←mul_assoc, congr_form]; rw [mul_assoc _ (star U.val), U.property.1,mul_one,mul_assoc _ (star V.val), V.property.1,mul_one] -- assoc tune
lemma gapStar {P:Op I}(h:Pᵀ= -P) : star P= -cc P:=by calc star P= cc Pᵀ:= by ext i j; simp
                                                                   _ = -cc P:=by rw [h,cc_neg]
namespace Bore
variable (h: Bore P C r)
include h
lemma nn : 0≤r:=(norm_nonneg _).trans h.low
lemma δ_pos:0<1-r^2:=by nlinarith only [h.hi,h.nn]
lemma cuts: (cutC P C)ᵀ= -cutC P C:= by
 unfold cutC; rw [Matrix.transpose_mul, Matrix.transpose_mul, ccT,h.p.isSelfAdjoint,h.sk,show Pᵀ=cc P by rw [cc,h.p.isSelfAdjoint], neg_mul,mul_neg,mul_assoc P]; -- tune
lemma bump: cutC P C*cc P=cutC P C∧ P*cutC P C=cutC P C:= ⟨body_right h.p C, body_left h.p C⟩
lemma bound_t : ‖P*C*(1-cc P)‖≤r:=by
 let X:= (1-P)*C*cc P; apply le_trans _ h.low
 rw [show P*C*(1-cc P)= -(cc (star X)) by
    rw [show cc (star X)=Xᵀ by simp [cc]]; unfold X; rw [ Matrix.transpose_mul,Matrix.transpose_mul,ccT,h.p.isSelfAdjoint,h.sk,Matrix.transpose_sub,Matrix.transpose_one, show Pᵀ=cc P by rw [cc,h.p.isSelfAdjoint], neg_mul,mul_neg,neg_neg,mul_assoc P]]
 rw [norm_neg,norm_cc,norm_star]; exact le_rfl
lemma turned(U:UNI I): Bore (twist U P) (congrC U C) r:=by
 refine ⟨⟨show _*_=_ from by rw [←map_mul,h.p.isIdempotentElem.eq],show star _ = _ from by rw [←map_star,h.p.isSelfAdjoint]⟩,?_, skew_form h.sk, ?_,h.hi⟩
 · rw [congr_form]; exact (unitary _).mul_mem ((unitary _).mul_mem U.property h.unit) (star (ccU U)).property
 rw [toll_twist,congr_norm]; exact h.low
lemma portion : let B:=P*C*(1-cc P); lost P C=B*star B:=by
 intro B; unfold lost B; rw [star_mul,star_mul,(ccProj h.p).one_sub.isSelfAdjoint,h.p.isSelfAdjoint]; simp only [←mul_assoc]; rw [mul_assoc (P*C) (1-_) (1-_),(ccProj h.p).one_sub.isIdempotentElem.eq]
lemma gram_eq : cutC P C*star (cutC P C)=P-lost P C:=by
 have hp:= h.p; unfold lost; unfold cutC; rw [star_mul, star_mul, (ccProj hp).isSelfAdjoint,hp.isSelfAdjoint,mul_sub (P*C),mul_one, sub_mul, sub_mul, mul_assoc P C (star C), h.unit.2,mul_one,hp.isIdempotentElem.eq]; simp only [←mul_assoc]; rw [mul_assoc (P*C), (ccProj hp).isIdempotentElem.eq]; abel -- tune
lemma PSD : 0 ≤ lost P C:=by rw [h.portion]; exact mul_star_self_nonneg _
lemma costs : ‖lost P C‖≤r^2:=by rw [h.portion]; apply (norm_mul_le ..).trans; rw [norm_star,← pow_two]; exact pow_le_pow_left₀ (norm_nonneg _) h.bound_t _
lemma hub : lost P C ≤ r^2 • (1:Op I):= (op_le_norm_one (IsSelfAdjoint.of_nonneg h.PSD)).trans (smul_le_smul_of_nonneg_right h.costs zero_le_one)
lemma robust : (1-r^2:ℝ) • (1:Op I)≤1-lost P C:=by rw [sub_smul,one_smul]; exact sub_le_sub_left h.hub _
lemma realG : IsUnit (1-lost P C):=(Spin.Pledge.Gap_inv h.δ_pos h.robust).1
lemma lot(U:UNI I): lost (twist U P) (congrC U C)=twist U (lost P C):=by
 let V:=ccU U; let P':=twist U P; let C':=congrC U C;
 have hx(U:UNI I)(C:Op I): congrC U C*star (congrC U C)=twist U (C*star C):=by rw [congr_form, twist_formula,star_mul,star_mul,star_star]; simp only [←mul_assoc]; rw [mul_assoc (U.val*C), (ccU U).property.1,mul_one]
 have he:= h.gram_eq; have hp:= (h.turned U).gram_eq; rw [forest,hx,he,map_sub] at hp; exact sub_right_injective hp.symm -- tune
end Bore
end YM.CF.BPress.Pf
