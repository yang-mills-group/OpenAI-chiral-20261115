import YM.CF.BPress.Spin.Cellar
/-! S²/W formula (B-pass,B-Suw), row space and norm price in terms of c. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spin.Cellar
open Function Filter NormedSpace Finset Fock Branch Dial Pledge Quad
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{c:ℝ}{A P Q R L D:Op I}
namespace Pass
def coeff1(P Q L:Op I)(u:ℝ):= P+u • L+u^2 • Q
def coeff0(Q L:Op I)(u:ℝ):= L+u • Q
def slide(P Q L A:Op I)(u:ℝ):=coeff1 P Q L u * rent1 P A+coeff0 Q L u * rent0 P A
def smoothP(P Q L A:Op I)(u:ℝ):=Trans.beam A (slide P Q L A u)
def ramp(L P A:Op I):=Trans.beam (rent0 P A) (L*rent0 P A)
def warp(P Q L:Op I)(u:ℝ):=u⁻¹ • P+u • Q+L

def magnet(c:ℝ):= c^2/3
lemma positivity_M (p:0<c): 0< magnet c:=by unfold magnet; positivity
lemma small_M (p:0<c)(q:c≤1): magnet c≤1:=by unfold magnet; nlinarith

variable (X:Pass P Q L A c) (u:ℝ)
include X
lemma topL: L* slide P Q L A u=u • (L*rent1 P A)+L*rent0 P A:=by
 unfold slide coeff1 coeff0; have f:=X.toEmpties; rw [mul_add,←mul_assoc,←mul_assoc L, mul_add,mul_add L P,mul_add L L]; simp only [f.LP, f.LQ,Algebra.mul_smul_comm,f.r.isIdempotentElem.eq,smul_zero,zero_add,add_zero,Algebra.smul_mul_assoc]
lemma topP: P*slide P Q L A u=P*rent1 P A:=by
 unfold slide coeff1 coeff0; have f:=X.toEmpties; simp only [mul_add,←mul_assoc P, Algebra.mul_smul_comm,f.p.isIdempotentElem.eq,f.PL,f.orth,smul_zero,zero_add,add_zero,zero_mul]
lemma rightP: slide P Q L A u*A=slide P Q L A u:=by unfold slide; rw [add_mul,mul_assoc,mul_assoc _ (rent0 P A),X.ray0',X.ray1']
omit X in
lemma realAct(a:ℝ)(P: Op I)(v:Ket I): acts (a • P) v=(a:ℂ) • acts P v:=by rw [← act_smul]; congr 2
lemma lower_norm (v: Ket I) (h:‖u‖≤1) : let S:= slide P Q L A u; magnet c*‖acts A v‖ ≤ ‖acts S v‖:=by
 intro S; let E:= X.toEmpties; let w₁:= acts (rent1 P A) v; let w₀:= acts (rent0 P A) v; have hz: acts A v=w₁+w₀:=by unfold w₀ w₁ rent0; rw [act_sub]; abel
 let y:=‖acts S v‖; have hy:0≤y:=norm_nonneg _; have he : acts (rent1 P A) w₁=w₁:= by unfold w₁; rw [←act_mul,X.r1.isIdempotentElem.eq]
 have ht : acts (rent0 P A) w₀=w₀:= by unfold w₀; rw [←act_mul,X.r0.isIdempotentElem.eq]
 have hp: c*‖w₁‖≤y:= (X.esc1 w₁ he).trans (by unfold w₁ y S; rw [←act_mul,←X.topP u,act_mul]; exact cheap_apply E.p _)
 have hx: c*‖w₀‖≤y+‖w₁‖:=by
    have hv: acts L w₀=acts L (acts S v)-(u:ℂ) • acts L w₁:=by unfold S w₀ w₁; rw [←act_mul L (slide P Q L A u),←act_mul L (rent1 P A), X.topL, act_add,realAct,add_sub_cancel_left,act_mul L (rent0 P A)]
    apply (X.vis_cap w₀ ht).trans; rw [hv]; apply (norm_sub_le ..).trans; rw [norm_smul,Complex.norm_real]; exact add_le_add (cheap_apply E.r _) ((mul_le_of_le_one_left (norm_nonneg _) h).trans (cheap_apply E.r _))
 rw [hz]; have hm: c*y≤y:= mul_le_of_le_one_left hy X.small; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) (positivity_M X.pos).le).trans; have hA:= add_le_add (mul_le_mul_of_nonneg_left hp X.pos.le) (mul_le_mul_of_nonneg_left hx X.pos.le); unfold magnet; change _ ≤ y; nlinarith
lemma enjoy (h:‖u‖≤1) : Trans.Ready ((magnet c)^2) A (slide P Q L A u):=by
 let S:= slide P Q L A u; let k:=magnet c; have hp:=positivity_M X.pos
 have he : k^2 • A ≤ star S*S:= by
    apply e_le _ (IsSelfAdjoint.star_mul_self S); swap; · rw [isSelfAdjoint_iff,star_smul,X.a.isSelfAdjoint,star_trivial]
    intro v; rw [e_scale,e_proj X.a,e_pow,←mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hp.le (norm_nonneg _)) (X.lower_norm u v h) _
 let ht:=pow_pos hp 2; exact ⟨X.a,X.rightP _,ht,coin X.a _ ht (pow_le_one₀ hp.le (small_M X.pos X.small)) he⟩
lemma stamped(h:‖u‖≤1): IsStarProjection (smoothP P Q L A u):=(X.enjoy u h).starP
lemma approves : slide P Q L A 1=A:=by
 unfold slide coeff1 coeff0; simp only [one_smul,one_pow]; rw [show P+L+Q=1 from (by rw [X.l0]; abel), show L+Q=1-P from (by rw [X.l0]; abel),sub_mul, X.cold]; unfold rent0; simp
lemma meeting : smoothP P Q L A 1=A:=by rw [smoothP,X.approves]; exact (Trans.Ready.atSelf X.a).2
lemma rapid (h:0<u): slide P Q L A u=warp P Q L u *(u • rent1 P A+rent0 P A):=by
 unfold slide; rw [mul_add,Algebra.mul_smul_comm, ←Algebra.smul_mul_assoc u]; unfold warp; simp only [smul_add,smul_smul,mul_inv_cancel₀ h.ne',one_smul]; unfold coeff1 coeff0; simp only [add_mul,pow_two,Algebra.smul_mul_assoc,X.cold,smul_zero]; abel
-- relations for s0 extended frame
lemma mid_zero1 : slide P Q L A 0* rent1 P A= P*rent1 P A:=by unfold slide coeff1 coeff0; norm_num1; simp only [zero_smul,add_zero,add_mul,mul_assoc, X.sap',mul_zero,X.r1.isIdempotentElem.eq]; -- tune
lemma mid_zero0 : slide P Q L A 0* rent0 P A=L*rent0 P A:=by unfold slide coeff1 coeff0; norm_num1; simp only [zero_smul,add_zero,add_mul,mul_assoc,X.sap,mul_zero,zero_add,X.r0.isIdempotentElem.eq]
lemma floor_S : slide P Q L A 0=P*rent1 P A+L*rent0 P A:=by unfold slide coeff1 coeff0; simp
lemma ramp_star : IsStarProjection (ramp L P A):= X.gate0.starP
lemma ramp_L: L*ramp L P A=ramp L P A:=by unfold ramp Trans.beam; rw [←mul_assoc, ←mul_assoc, X.toEmpties.r.isIdempotentElem.eq]
lemma ramp_P: P*ramp L P A=0:=by nth_rw 1 [← X.ramp_L]; rw [←mul_assoc,X.toEmpties.PL,zero_mul]
-- B-Ppass
lemma mark_exit : smoothP P Q L A 0= P+ramp L P A:=by
 let S:= slide P Q L A 0; let J:= smoothP P Q L A 0; let W:= ramp L P A; have t:= X.enjoy 0 (by simp)
 have he: J*S=S:= t.continuousSpace
 have h: IsStarProjection (P+W):= climax X.p X.ramp_P X.ramp_star; apply le_antisymm
 · apply (t.starP.le_iff_mul_eq_right h).mpr
   have hp: (P+W)*S=S:=by
      have hg: W*(L*rent0 P A)=L*rent0 P A:= X.gate0.continuousSpace
      unfold S; rw [X.floor_S,mul_add,add_mul,←mul_assoc P P,←mul_assoc W,back X.p X.ramp_star X.ramp_P,X.p.isIdempotentElem.eq,zero_mul,add_zero,add_mul _ _ (L*_),hg,←mul_assoc P,X.toEmpties.PL,zero_mul,zero_add]
   change (P+W)*(S* _) = _; rw [←mul_assoc,hp]; rfl -- tune
 apply (h.le_iff_mul_eq_right t.starP).mpr
 let D:=star (Trans.pinv P (A*P)); have hp: J*P=P:=by
    have hA:S*rent1 P A* D=P:=by unfold S; rw [X.mid_zero1]; exact X.opens
    nth_rw 1 [← hA]; rw [←mul_assoc J, ←mul_assoc J,he,hA]
 have hx:J*(L*rent0 P A)=L*rent0 P A:=by rw [← X.mid_zero0, ←mul_assoc,he]
 change J*(P+W)=P+W; rw [mul_add,hp, show W=(L*rent0 P A)*_ from rfl,←mul_assoc J,hx] -- tune
end Pass
end YM.CF.BPress.Spin.Cellar
