import YM.SU5.FiniteGaugeData.Cuprite.Spiny
import YM.CF.Flare.Dice
/-! # WP18: field-one slope of insertion, genuine chiral comparator. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Fock.Relief
open Function Filter Finset NormedSpace MeasureTheory
open Thera Reduction Reduction.Hutch Reduction.Drama.Pack Reduction.Drama Reduction.Jersey Cascade
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*}
section crisp
variable [Fintype n][LinearOrder n]{Q P K K' D W:Op n}{b a:ℝ}{T:Finset n}
abbrev Model(Q P:Op n) := lit (spring Q (Q*P))
structure Standing(Q P:Op n):Prop where
 carpet : IsStarProjection Q
 hedge : IsStarProjection P
 balance : Q.trace=P.trace
 litA : Model Q P
abbrev tuneC(Q P:Op n)(K:Op n):Prop:= Clad P Q 1 1 K
namespace TuneC
variable (h:tuneC Q P K)
include h
lemma low : P*K=K := h.tray
lemma up : K*P=P := by rw [←h.stem,mul_assoc]; exact (Q.mul_one ▸ h.left) -- tune signature
lemma crisp : Q*K=Q := by rw [←h.tray,←mul_assoc]; simpa using h.right
lemma mirror : tuneC (1-Q) (1-P) (1-star K):=by
 let T:=1-star K; let X:=1-Q; let Y:=1-P; let v0:=Q*K
 have hx: (1-P)*(1-star K)=1-star K:=by
    have he:P*star K=P:=by nth_rw 1 [←show star P=P from h.proj.2]; rw [←star_mul, up h,h.proj.2];
    rw [sub_mul,one_mul,mul_sub,mul_one,he,sub_self,sub_zero]
 have hh: (1-star K)*(1-Q)=1-star K:=by
    have he:star K*Q=Q:=by nth_rw 1 [←show star Q=Q from h.helm.2]; rw [←star_mul, crisp h,h.helm.2]
    rw [mul_sub,mul_one,sub_mul,one_mul,he,sub_self,sub_zero]
 have hu: (1-star K)*(1-P)=1-P :=by
    have he:star K*P=star K:=by nth_rw 1 [←show star P=P from h.proj.2]; rw [←star_mul,low h];
    rw [sub_mul,one_mul,mul_sub,mul_one,he,sub_self,sub_zero]
 have hp: (1-Q)*(1-star K)=1-Q :=by
    have he:Q*star K=star K:=by nth_rw 1 [←show star Q=Q from h.helm.2]; rw [←star_mul,h.stem]
    rw [mul_sub,mul_one,sub_mul,one_mul,he,sub_self,sub_zero]
 exact ⟨h.proj.one_sub,h.helm.one_sub,by simp,by rw [mul_one,←mul_assoc,hh,hu],by rw [mul_one,mul_assoc,hx,hp],hx, hh⟩
lemma rotates(U:UNI n): tuneC (twist U Q) (twist U P) (twist U K):=by
 refine ⟨h.proj.map (twist U),h.helm.map (twist U),by simp,?_,?_,?_,?_⟩
 · simp only [mul_one,←map_mul, ←mul_assoc K,h.stem, up h]
 · simp only [mul_one,←map_mul,mul_assoc Q P K,h.tray, crisp h]
 · rw [←map_mul,h.tray]
 rw [←map_mul,h.stem]
lemma bow (p:tuneC Q P K'):K=K':=by
 have he:K*K'=K:=by nth_rw 1 [←h.stem]; rw [mul_assoc,crisp p,h.stem]
 rw [← he]; nth_rw 1 [←p.tray]; rw [←mul_assoc,up h,p.tray]
end TuneC
local notation "Θ"=> spring Q (Q*P)
def oblique(Q P:Op n):Op n:= star (Q*P)*(spring Q (Q*P))⁻¹*Q
local notation "J"=> oblique Q P
abbrev cup(Q P:Op n)(D:Op n):ℂ:=(oblique Q P*D).trace
lemma cup_zero : cup Q P 0=0:=by unfold cup; rw [mul_zero,Matrix.trace_zero]
lemma cup_smul (Q P D:Op n)(c:ℂ) : cup Q P (c• D)=c*cup Q P D:=by unfold cup; rw [Matrix.mul_smul,Matrix.trace_smul]; rfl
lemma cup_sum {I:Type*}(D:I→ Op n)(Q P:Op n)(A:Finset I):cup Q P (∑ i∈A,D i)=∑ i∈A,cup Q P (D i):=by unfold cup; rw [mul_sum,Matrix.trace_sum]
lemma cup_sub(Q P X Y:Op n):cup Q P (X-Y)=cup Q P X-cup Q P Y:=by unfold cup; rw [mul_sub,Matrix.trace_sub]
variable (p:Standing Q P)
namespace Standing
include p
lemma luxury: tuneC Q P (oblique Q P):=by
 have hp:= Flare.bridge (N:=Q*P) p.hedge p.carpet p.balance (show star (1:Op n)*1=1 by simp) (a:=1) (by norm_num) (by rw [mul_one, inv_one,one_smul]) (lit_mulin p.litA); rw [inv_one,one_smul] at hp; exact hp
lemma reverberates: (cup Q P (W-1)).re=curlR Q P W:=by
 let X:=W-1; let A:=Q*P; let D:=Q*X*P; let H:=Θ⁻¹; change TrR ((_ * H * Q)*(W-1))=TrR (H*(A*star D)); -- ambiguous _
 rw [TrR_cov (show star H=H from IsSelfAdjoint.of_nonneg (lit_inv p.litA).1) A D,TrR_comm H]; change TrR ( (star A*H*Q)*X)=TrR ((D*star A)*H)
 have h0:P*star A=star A:=by unfold A; rw [star_mul, p.hedge.2, ←mul_assoc,p.hedge.1]
 unfold D; rw [mul_assoc (Q*X),h0, mul_assoc (star A*H), TrR_comm (star A*H),mul_assoc (Q*X)]
lemma priceD(U:UNI n)(hp:twist U (1-Q)=Q)(hq:twist U (1-P)=P)(hv:D.trace=0) : cup Q P (-twist U (star D))=star (cup Q P D):=by
 let K0:=twist U; let T:= K0 (1-star J); have hz:= TuneC.rotates (TuneC.mirror p.luxury) U; rw [hp,hq] at hz
 have hE:T=J:= TuneC.bow hz p.luxury
 nth_rw 1 [cup]; rw [mul_neg, Matrix.trace_neg]; nth_rw 1 [←hE]; unfold T K0; rw [←map_mul,trace_twist,sub_mul,one_mul,Matrix.trace_sub]; have he(X:Op n): Matrix.trace (star X) =star (Matrix.trace X):= by rw [Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
 rw [←star_mul,he D,hv,star_zero, he, Matrix.trace_mul_comm D J, zero_sub,neg_neg]
end Standing
end crisp
section patron
variable [LinearOrder n] [Fintype n]{Q P X:Op n}{x p:Wave n}
variable (h:Standing Q P) (hx:Sea P x)(hp:Sea Q p)
local notation "T"=> oblique Q P
include h hx hp
lemma frank (u v:Ket n): inner ℂ p (acts (create u * remove v) x)=inner ℂ v (acts (oblique Q P) u)* inner ℂ p x:= by
 let y:= acts T u; have ht:= h.luxury; have he:acts P y=y:=by unfold y; rw [←act_mul, ht.tray]
 let g:=u-y; have hw:acts Q g=0:=by unfold g y; rw [map_sub,←act_mul,TuneC.crisp ht,sub_self]
 have h0:inner ℂ p (acts (create g*remove v) x)=0:= by rw [act_mul,←act_inner]; change inner ℂ (acts (remove g) p) _=_ ; rw [tars h.carpet hp.1 hw,inner_zero_left]
 rw [show u=g+y from (sub_add_cancel ..).symm]; -- danger RHS
 change _=inner ℂ v (acts T (g+y))*_; rw [show acts T (g+y)=y from (show _= _ from ?_)] -- u accidental.Intent `nth_rw`, simplify
 rw [map_add,add_mul,act_add,inner_add_right,h0,zero_add]
 rw [show create y*remove v=_ from eq_sub_of_add_eq' (car v y),act_sub,act_mul,tarp h.hedge hx.1 he,map_zero,sub_zero,act_smul,act_one,inner_smul_right]
 rw [show g+y=u from sub_add_cancel ..];
lemma tension(X:Op n): inner ℂ p (acts (dg X) x)=cup Q P X *inner ℂ p x:=by
 nth_rw 1 [← mul_one X, ←star_one (R:=Op n)]; rw [prizeUV,act_sum,inner_sum] -- inner_sum? check
 simp_rw [act_one,frank h hx hp,←act_mul,basis_inner,basis_act, ←sum_mul]; rfl
lemma vision(X:Op n):inner ℂ p x≠0 ∧ inner ℂ p (acts (dg X) x)/inner ℂ p x=cup Q P X:=by
 have he:= shines h.luxury x p hx hp; unfold skyGlow at he; rw [quant_one,act_one] at he; exact ⟨he,(div_eq_iff he).mpr (tension h hx hp X)⟩
-- Uniform bill on any fixed support independent of height.M.
omit hx hp
variable {A:ℝ}{S:Finset n}
lemma aperture [Nonempty n](p:pointM n Q P A)(i:n): ‖acts T (basisKet i)‖ ≤ 1+A:=by
 let x:=basisKet i; let U:=Q*P; let J:=spring Q U; let R:=tangle J; have hp:= h.luxury; let F:= R*U; have ht:F*star F≤1:=by
    rw [star_mul,show star R=R from refl_star (lit_inv h.litA).1] -- let needed `change..` tunes
    apply le_trans (b:=R*J*R) _ (le_of_eq (tangle_n h.litA))
    rw [←mul_assoc, mul_assoc R U]; -- tune
    exact IsSelfAdjoint.of_nonneg (show 0≤R from refl_nn (lit_inv h.litA).1)|>.conjugate_le_conjugate (le_add_of_nonneg_right h.carpet.one_sub.nonneg)
 have he: ‖F‖≤1:= own2 F zero_le_one (by rw [one_pow,Canon,one_smul]; exact ht); let G:=R*(Q*(1-P)); have hz: T=P+star F * G:=by
    unfold F G; rw [star_mul,show star R=R from refl_star (lit_inv h.litA).1,←mul_assoc, mul_assoc (star U) R, show R*R=J⁻¹ from intake_t h.litA]; change T=P+star U*J⁻¹*(Q*(1-P)); rw [←mul_assoc]; change T=P+T*(1-P); rw [mul_sub,mul_one,TuneC.up hp]; abel
 have hl: ‖acts P x‖≤1:=by refine ((acts P).le_opNorm x).trans ?_; rw [show ‖x‖=1 by simp [x,basisKet], mul_one]; exact h.hedge.norm_le _
 have hw: ‖acts (star F*G) x‖≤ A:= by rw [act_mul]; exact ((acts (star F)).le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) ((norm_star F).trans_le he)).trans (p i))
 rw [hz,act_add]; exact (norm_add_le ..).trans (add_le_add hl hw)
lemma cardPay [Nonempty n](p:pointM n Q P A)(X:Op n)(hx:cutM S *X=X) : ‖cup Q P X‖ ≤ S.card * (1+A)*‖X‖:=by
 let J:= X*T; unfold cup; rw [Matrix.trace_mul_comm]; change ‖∑ i:n,J i i‖ ≤_; let f:= fun i:n=> ‖J i i‖; apply le_trans (norm_sum_le ..); rw [←sum_subset (subset_univ S) (f:=f) ?_] -- tune does f automatch?
 apply (sum_le_sum (g:=fun _=> (1+A)*‖X‖) (fun i v=>?_)).trans_eq; · rw [sum_const,nsmul_eq_mul,mul_assoc]
 unfold f; rw [basis_b J i,show J=X*T from rfl,act_mul]; apply le_trans (norm_inner_le_norm ..); rw [show ‖basisKet i‖=1 by simp [basisKet],one_mul, mul_comm (1+A)]; refine ((acts X).le_opNorm _).trans (mul_le_mul_of_nonneg_left (aperture h p i) (norm_nonneg _))
 intro i _ hw; unfold f J; rw [←hx, mul_assoc, cutM,Matrix.diagonal_mul]; simp [hw]
#print axioms vision
#print axioms cardPay
end patron
end YM.CF.Fock.Relief
