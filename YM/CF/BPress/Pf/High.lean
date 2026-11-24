import YM.CF.BPress.Spin.Trans
import YM.CF.BPress.Spin.Grading
import YM.CF.Sedge.Aurum
/-! Slater amplitude in the actual quantizer. Do not normalize except once by the relative log price. The `floatW` formula is on a nonzero ket, one actual occupied projector at this regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A:Op I}{x:Wave I}{ε:ℝ}
structure Top (P:Op I)(v:Wave I):Prop where
 star:IsStarProjection P
 line: acts (lineOp P) v=v
 live:v≠0
lemma topOnSea (p:IsStarProjection P)(h:Sea P x) : Top P x:=⟨p,h.1,norm_pos_iff.mp (zero_lt_one.trans_eq h.2.symm)⟩
namespace Top
variable (p: Top P x)
include p
lemma occupies : acts (quant P) x=x:=by nth_rw 1 [←p.line]; rw [←act_mul,line_quant p.star,p.line]
lemma usable : ∃ (U:UNI I)(s:Finset I)(c:ℂ), P=twist U (cutM s)∧ c ≠ 0 ∧ x=c • wedge U.val s:=by
 obtain ⟨U,s,H⟩:=spot_projection P p.star; have hu:x=inner ℂ (wedge U.val s) x • wedge U.val s:=by nth_rw 1 [←p.line]; rw [H,act_twistLine]
 refine ⟨U,s,_,H,?_ , hu⟩; intro E; exact p.live (by nth_rw 1 [hu]; rw [E,zero_smul])
lemma spread (h:Trans.Ready ε P A) : Top (Trans.beam P A) (acts (quant A) x):=by
 refine ⟨h.starP, ?_, ?_⟩; swap
 · intro l; have he:= congrArg (acts (quant (Trans.pinv P A))) l; rw [←act_mul, ←quant_mul, h.paid,p.occupies, map_zero] at he; exact p.live he
 let L := Trans.beam P A; let X := quant A; nth_rw 1 [←p.line]; rw [←act_mul X, ←act_mul, show lineOp L*(X*lineOp P)= X*lineOp P from ?_, act_mul,p.line]
 have he : lineOp L*X=X*lineOp P:=by
    rw [lineOp,h.trace,lineOp]; unfold X
    let F:= ∑ k∈range (Fintype.card I+1), chooseK (Fintype.card I) k P.trace • selector I k
    have ht : quant A*F=F*quant A:=by unfold F; simp_rw [mul_sum,sum_mul, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,selector_quant]
    rw [mul_assoc,← ht,←mul_assoc, ←mul_assoc,←quant_mul, ← quant_mul,h.continuousSpace,h.tag]
 rw [←mul_assoc,he,mul_assoc,(line_proj p.star).isIdempotentElem.eq]
lemma seaNorm (U:UNI I)(s:Finset I)(h:P=twist U (cutM s)): ‖inner ℂ (wedge U.val s) x‖=‖x‖:= by conv_rhs=> rw [←p.line,h,act_twistLine]; rw [norm_smul,wedge_norm,mul_one] -- tune
end Top

def terrace (P T: Op I) := P*T*P+(1-P)
lemma ter_frame(U:UNI I)(P T:Op I): terrace (twist U P) (twist U T)=twist U (terrace P T):= by unfold terrace; simp
lemma frame_value(U:UNI I)(s:Finset I)(M:Op I):inner ℂ (wedge U.val s) (acts (quant M) (wedge U.val s))=(terrace (twist U (cutM s)) M).det:=by
 let V:=twist U (cutM s); rw [←det_twist (star U),←ter_frame,twist_inv]; rw [show terrace (cutM s) (twist (star U) M)=padded s (twist (star U) M) from rfl, ←Fock.principal]; rw [←quant_column]
 let A:=quantU U; change inner ℂ (acts A.val _) _=_; nth_rw 1 [← star_star A.val]; rw [act_inner, ←act_mul, ←act_mul,basis_inner,basis_act,quant_twist,twist_formula,quantU_star]; change _ = (star A.val*_*star (star A.val)) _ _; rw [star_star]; rfl -- tune
lemma operates (p:Top P x)(h:P*A=A*P): acts (quant A) x=(terrace P A).det • x:=by
 obtain ⟨U,s,c,rfl,u,rfl⟩:= p.usable; let v:= wedge U.val s; let B:=lineOp (twist U (cutM s)); have hp: acts B v=v:=by rw [act_twistLine,show inner ℂ (wedge U.val s) v= (1:ℂ) by rw [inner_self_eq_norm_sq_to_K, wedge_norm]; simp, one_smul]
 let d:=(terrace (twist U (cutM s)) A).det; rw [map_smul]; have hk:acts (quant A) v=d • v:=by nth_rw 1 [←hp]; rw [←act_mul,line_quant_comm h.symm,act_mul,act_twistLine, frame_value]
 rw [hk,smul_comm]
lemma tall_norm (p:Top P x)(A:Op I): ‖acts (quant A) x‖^2=‖x‖^2 * ‖(terrace P (star A*A)).det‖:=by
 let F:=quant A; obtain ⟨U,s,c,hp,f,e⟩:=p.usable; let v:= wedge U.val s; rw [e,map_smul,norm_smul,norm_smul,wedge_norm, mul_one,mul_pow]
 have hc: inner ℂ (acts F v) (acts F v)=(terrace P (star A * A)).det:=by nth_rw 1 [←star_star F]; rw [act_inner, ←act_mul]; rw [show star F*F=quant (star A*A) from by rw [quant_mul,quant_star],hp]; exact frame_value U s _
 congr 1; rw [← hc,inner_self_eq_norm_sq_to_K,norm_pow]; simp [Complex.norm_real]; rfl -- tune
lemma floatW (h:Top P x)(p:Trans.Ready ε P A): ‖acts (quant A) x‖^2= ‖x‖^2* ‖(Trans.gram P A).det‖:=by rw [tall_norm h]; unfold terrace Trans.gram; rw [←mul_assoc P,p.tagS,mul_assoc,p.tag]
-- tilted path through dΓ actually applied; use all real u (not exponent log norm).
lemma drift(A:Op I)(h:A*A=0)(u:ℝ): quant (1+u • A)=exp (u • dg A):=by rw [←dg_scale, tallied (u • A) (by rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,h,smul_zero,smul_zero])]
lemma together (h:Top P x)(A:Op I): acts (quant A) x =acts (quant (A * P)) x:=by rw [quant_mul,act_mul,h.occupies]
end YM.CF.BPress.Pf
