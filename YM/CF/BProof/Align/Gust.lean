import YM.CF.BProof.Align.Fit

/-! From ms shear T and Z(u), use S=Z(u)A. Price locality independent d; inherit
anti-intertwining via operator-norm difference from upright A. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Align
open Function Filter Fock Finset Branch
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[DecidableEq I][Fintype I] {P J T:Op I}
def bend (P T:Op I)(u:ℝ):=1+u • T
def slit (P T:Op I)(u:ℝ) := bend P T u*P
def gust (P J:Op I) := (1-P)*J*P
def Gust (P T:Op I) : Prop := IsStarProjection P ∧ T*P=T ∧ P*T=0
lemma gustH (h:IsStarProjection P)(J: Op I) : Gust P (gust P J):= ⟨h,by rw [gust,mul_assoc,h.isIdempotentElem],by rw [gust, ←mul_assoc P,←mul_assoc P, Porth h]; simp⟩
namespace Gust
variable (g:Gust P T)(u:ℝ)
include g
lemma square : T*T=0:=by nth_rw 1 [←g.2.1]; rw [mul_assoc,g.2.2,mul_zero]
lemma rise : slit P T u=P+u • T:= by rw [slit,bend,add_mul,one_mul,Algebra.smul_mul_assoc,g.2.1]
lemma floor : slit P T u * P=slit P T u:=by rw [slit,mul_assoc,g.1.isIdempotentElem]
lemma voice : entered P (slit P T u)=1+ u^2 • (star T*T) := by
 have he:star T*P=0:=by nth_rw 1 [←g.1.isSelfAdjoint.star_eq]; rw [←star_mul,g.2.2,star_zero]
 rw [entered,g.rise,star_add,g.1.isSelfAdjoint,star_smul,star_trivial]
 simp only [add_mul,mul_add,g.1.isIdempotentElem.eq,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,g.2.2,he,smul_zero]; rw [pow_two,mul_smul u u]; abel
lemma bound : 1≤ entered P (slit P T u):= by rw [g.voice,le_add_iff_nonneg_right]; exact smul_nonneg (sq_nonneg u) (star_mul_self_nonneg _)
lemma fit : Fit P (slit P T u):= ⟨g.1,g.floor u,active one_pos (by rw [one_smul]; exact g.bound u)⟩
lemma closet {u:ℝ} [Nonempty I] (p:‖u‖≤1)(h:‖T‖≤1): ‖land P (slit P T u)-P‖≤4*‖T‖:=by
 let S:= slit P T u; let A:= entered P S; let X:=A⁻¹
 have he:‖S-P‖≤‖T‖:=by rw [show S=_ from g.rise u,add_sub_cancel_left,norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) p
 have hx: ‖X‖≤1:=by simpa only [inv_one] using invNorm (by norm_num : 0<(1:ℝ)) (A:=A) (by rw [one_smul]; exact g.bound u)
 have hP:=g.1.norm_le P
 have hs: ‖S‖≤ 2:= by simpa using le_trans (norm_le_norm_sub_add S P) ((add_le_add (he.trans h) hP).trans (by norm_num)) -- tune
 have hz: ‖X-1‖≤ ‖T‖:=by
    have hl : X*A=1:= (live (g.fit u).active).2; rw [show X-1=X*(1-A) from (by rw [mul_sub,mul_one,hl]),show A=_ from g.voice u,show 1- (1+u^2 • (star T*T))= -(u^2 •(star T*T)) from by abel]; apply (norm_mul_le ..).trans; rw [norm_neg,norm_smul,norm_pow]; apply (mul_le_of_le_one_left (by positivity) hx).trans ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) p)).trans ?_); exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (by rwa [norm_star]))
 have hp : ‖star S-P‖ ≤ ‖T‖:= by rw [←g.1.isSelfAdjoint.star_eq, ←star_sub,norm_star]; exact he
 change ‖land P S-P‖≤_; rw [show land P S-P= (S-P)*X*star S+P*(X*(star S-P))+P*((X-1)*P) from ?_]; swap; · change S*(X*star S)-P=_; rw [sub_mul,sub_mul ((S)*X) ((P)*X),mul_sub X,sub_mul X 1 P,one_mul,mul_sub P,mul_sub P,g.1.isIdempotentElem,mul_assoc P,mul_assoc S]; abel
 apply (norm_add_le ..).trans; refine (add_le_add ((norm_add_le ..).trans (add_le_add ?_ ?_)) ?_).trans_eq (show ‖T‖*2+‖T‖+‖T‖=_ from by ring)
 · apply (norm_mul_le ..).trans (mul_le_mul _ (show ‖star S‖ ≤2 by rwa [norm_star]) (norm_nonneg _) (norm_nonneg _)); exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hx).trans he)
 · exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hP).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hx).trans hp)))
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hP).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hP).trans hz)))
end Gust
end YM.CF.BProof.Align
