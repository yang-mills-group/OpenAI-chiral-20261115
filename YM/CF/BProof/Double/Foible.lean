import YM.CF.BProof.Double.Circuit
/-! angle criterion independent of dimension. Use `flip` to identify the two margins. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I] {A P Q C:Op I}{c r:ℝ} {x:Book I}
lemma flip_mono {P Q:M I}(h:P≤Q): flip P ≤ flip Q:=by
 apply (star_left_conjugate_le_conjugate (cc_mono h) (slip I)).trans' ?_ |>.trans ?_ <;> simp only [flip_star,flip,le_refl]
lemma flip_smr (A:M I)(u:ℝ) : flip (u • A)=u • flip A:=by rw [flip,cc_rsmul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rfl
def angle (c r:ℝ):=1-((debt c r)⁻¹)^2
def margin (c r:ℝ):= 1- Real.sqrt (angle c r)
lemma angle_pos (g:0<c)(h:r<1):0≤angle c r:= by have ht:=debt_one g h; have he:0<debt c r:=zero_lt_one.trans_le ht; apply sub_nonneg.mpr; apply pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ ht)
lemma margin_pos (g:0<c)(h:r<1): 0<margin c r:=by
 have hp:0<debt c r:=zero_lt_one.trans_le (debt_one g h); have ht:0<((debt c r)⁻¹)^2:=by positivity
 apply sub_pos.mpr; apply (Real.sqrt_lt' zero_lt_one).2 (by unfold angle; linarith)
lemma restrictNorm {T L:M I}(h:IsStarProjection T)(e:IsStarProjection L)(C:ℝ)(p:1≤C)(v:∀ x:Book I,let t:=acts T x;‖t‖≤ C*‖acts (1-L) t‖) : T*L*T ≤ (1-C⁻¹^2) • T:=by
 refine by_hil ?_ ?_ ?_
 · unfold IsSelfAdjoint; rw [star_mul,star_mul, h.isSelfAdjoint,e.isSelfAdjoint,mul_assoc]
 · unfold IsSelfAdjoint; rw [star_smul,h.isSelfAdjoint,star_trivial (1-C⁻¹^2)]
 intro x; let t:=acts T x; rw [hil_linear,hil_idem x h,inGram h e]; have hv:= splitOrth t e; have hp:0<C:=zero_lt_one.trans_le p; have ht: ‖acts (1-L) t‖^2 ≥ (C⁻¹* ‖t‖)^2:=by apply pow_le_pow_left₀ (mul_nonneg (inv_pos.mpr hp).le (norm_nonneg _)); exact (inv_mul_le_iff₀ hp).mpr (v x)
 change ‖acts L t‖^2 ≤ _ * ‖t‖^2; rw [mul_pow] at ht; linarith
-- square proof by splitting algebra
lemma priceFrame {R L:M I}(h:IsStarProjection R)(q:IsStarProjection L){a:ℝ}(p:0≤a)(v:R*L*R ≤ a • R)(w:(1-R)*(1-L)*(1-R) ≤ a • (1-R)): ‖R+L-1‖ ≤ Real.sqrt a:=by
 let A:=R+L-1; have ht: star A*A=R*L*R+(1-R)*(1-L)*(1-R):=by
    rw [show star A=A from ((h.isSelfAdjoint.add q.isSelfAdjoint).sub (show IsSelfAdjoint (1:M I) from star_one _)).star_eq]; unfold A; noncomm_ring [h.isIdempotentElem.eq,q.isIdempotentElem.eq] -- tune
 have hh : ‖A‖*‖A‖≤a:=by rw [← CStarRing.norm_star_mul_self]; refine betweenNorm p (star_mul_self_nonneg _) ?_; rw [ht]; apply (add_le_add v w).trans_eq; rw [← smul_add,add_sub_cancel]
 change ‖A‖≤_; nlinarith only [norm_nonneg A,Real.sq_sqrt p,Real.sqrt_nonneg a,hh]
namespace Deck
variable (p: Double.Deck A P Q C c r)
include p
lemma lowR : penR A*penL P Q C*penR A ≤ angle c r • penR A:=by
 let R:=penR A; let L:=penL P Q C; let Z:=projRight p.cbP.a; apply restrictNorm Z p.project _ (debt_one p.cbP.nice p.safety.lid); intro x t; apply p.curve (x:=t) (y:=acts L t) ((realEnter ..).mpr (selfApply Z x)) (p.coffin t) ; rw [act_sub,act_one]
lemma lowL : (1-penR A)*(1-penL P Q C)*(1-penR A)≤ angle c r • (1-penR A):=by
 have ht:=flip_mono p.lowR; simp only [flip_prod,p.reflectedLeft, reflectedRight,flip_smr] at ht; exact ht
lemma fort : ‖penR A + penL P Q C-1‖≤ Real.sqrt (angle c r):= priceFrame (projRight p.cbP.a) p.project (angle_pos p.cbP.nice p.safety.lid) p.lowR p.lowL
lemma reserve : margin c r • (1:M I)≤ penR A+penL P Q C:=by
 have ht:= op_ge_neg_scalar (((projRight p.cbP.a).isSelfAdjoint.add p.project.isSelfAdjoint).sub (show IsSelfAdjoint (1:M I) from star_one _)) p.fort; unfold margin; rw [sub_smul,one_smul]; exact le_trans (Eq.le (by abel : (1:M I)- _= -(Real.sqrt (angle c r) • (1:M I))+1)) (le_sub_iff_add_le.mp ht)
end Deck
end YM.CF.BProof.Double
