import GaugeFieldConstruction.Celadon
/-
X2 derivative before normalization. Avoids d.frame/choice. At horizontal pulse split lineOp*A. Uses unit 
predecessor only at the point computing the derivative, via stageI Floe.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fock.Celeb
open Filter NormedSpace Function Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ContDiff Topology
attribute [local instance] opCStarAlgebra
open BProof.Wick
variable {I:Type*}[Fintype I][LinearOrder I]
def CapeD (A C GA GC:Op I):Op I:= (GA*C+A*GC)*cc A + A*C*cc GA
def Sobiq (A C GA GC:Op I):ℂ:= (body A (CapeD A C GA GC)*(stage A C)⁻¹).trace / 2
abbrev dir_g (A GA:Op I):= GA*A-A*GA
variable (F C:ℝ→Op I)(x:ℝ){f c:Op I}(hF:HasDerivAt F f x)(hC:HasDerivAt C c x)(hP:∀ᶠ i in 𝓝 x,IsStarProjection (F i))(H:∀ᶠ i in 𝓝 x,(C i)ᵀ= -(C i))(Hp:IsUnit (stage (F x) (C x)))(Hu:filled (F x) (C x)≠0)
local notation "T"=> lineOp (F x)
local notation "qv"=> Sobiq (F x) (C x) f c
local notation "J"=> dir_g (F x) f
local notation "ρf" t:max=> filled (F t) (C t)
include H Hp Hu hF hC hP
lemma Prime_Q : HasDerivAt (fun t=>ρf t) (acts (dg J) (ρf x) + qv • (ρf x)) x:=by
 let L:=T; have ht:IsStarProjection (F x):= hP.self_of_nhds
 let A:=fun t=>ρf t; let A' := deriv A x; let B:= fun t=>body (F t) (C t)
 have hd: HasDerivAt A A' x:=by
    have he:DifferentiableAt ℝ A x:=by
        let R(t):=lineOp (F t); have hr:DifferentiableAt ℝ R x:=(Lamp_J hP hF).differentiableAt
        exact (((actCL _).differentiableAt.comp x hr).clm_apply ((pair_c.differentiable (by simp) _).comp x hC.differentiableAt)) -- tune
    exact he.hasDerivAt
 have hf:∀ᶠ t in 𝓝 x, acts (lineOp (F t)) (A t)=A t:=by
    filter_upwards [hP] with i hv; change acts _ (acts _ _)= _; rw [←act_mul,(line_proj hv).isIdempotentElem]; rfl
 have hw:acts T (A x)= A x := hf.self_of_nhds
 have hk:T*dg J*T=0:= Lamp_k hP hF
 have hg:A'=acts (dg J) (A x)+acts T A':=by
    let Q:= ((act_der (Lamp_J hP hF) hd).congr_of_eventuallyEq (hf.mono fun _ v=> v.symm)).deriv; change A'=acts (dg J*T - T*dg J) (A x)+acts T A' at Q
    have he:acts (T*dg J) (A x)=0:=by nth_rw 1 [←hw]; rw [←act_mul,hk,act_zero]
    rw [show dg J*T-T*dg J= _ from sub_eq_add_neg ..,act_add,act_neg,he,act_mul,hw,neg_zero,add_zero] at Q; exact Q
 let K' :=CapeD (F x) (C x) f c
 have hβ:HasDerivAt B K' x:=by
    let V:Op I→L[ℝ]Op I:=(⟨⟨cc,cc_add⟩,fun _ _=>cc_rsmul ..⟩: Op I→ₗ[ℝ]Op I).toContinuousLinearMap
    exact (hF.mul hC).mul (show HasDerivAt (fun t=> cc (F t)) (cc f) x from V.hasFDerivAt.comp_hasDerivAt x hF)
 let G(t):= relay (F x) (C x) (B t)
 have hi:G x=1:=by
    change relay (F x) (C x) (body _ _)=1
    nth_rw 1 [← relay_base ht Hp] -- ? no? 
    unfold relay
    rw [show body (F x) _ = body (F x) (C x) from (congrArg (fun z=>z*cc (F x)) (body_left ht _)).trans (body_right ht _)] -- tune 
 let S:= body (F x) K'*(stage (F x) (C x))⁻¹
 have hr : HasDerivAt G S x:=by unfold G S relay body; exact (((((hβ.const_mul _).mul_const _).mul_const _).add_const _))
 have hl:HasDerivAt (fun x=> (G x).det) (Matrix.trace S) x:=by
    have hx:= Aroma.TaylorA (show IsUnit (G x) from hi.symm ▸ isUnit_one) hr; rw [hi] at hx; simpa using hx
 obtain ⟨U,s,hs⟩:= spot_projection (F x) ht
 let Z:= wedge U.val s; let W(t):=stratum U s (B t); have h₀:A x=stratum U s (C x) • Z:=by unfold A; rw [hs,placed]
 have ha:∀ᶠ i in 𝓝 x,acts L (A i)= W i • Z:=by
    have h':∀ᶠ i in 𝓝 x,‖F x-F i‖<1:= (hF.continuousAt.eventually (Metric.ball_mem_nhds _ zero_lt_one)).mono fun i (q:dist (F i) (F x)<1) => by rwa [norm_sub_rev, ←dist_eq_norm]
    filter_upwards [h',hP] with i h hp; rw [show acts L (A i)=filled (F x) (B i) from Delta.area _ ht hp h,show filled (F x) (B i)=filled (twist U (cutM s)) (B i) from by nth_rw 1 [hs],placed]
 have Z':Z ≠0:=norm_pos_iff.mp ((wedge_norm U s).symm ▸ zero_lt_one : 0< ‖Z‖)
 let w:=stratum U s (C x); have hp:W x=w:= smul_left_injective ℂ Z' ((ha.self_of_nhds).symm.trans (hw.trans h₀)); have hf:w≠0:=by intro h; apply Hu; change A x=0; rw [h₀]; change w • Z=_; rw [h,zero_smul]
 let w':=deriv W x; have hS: HasDerivAt W w' x:= (((innerSL ℂ Z).restrictScalars ℝ).differentiableAt.comp x ((pair_c.differentiable (by simp) _).comp x hβ.differentiableAt): DifferentiableAt ℝ W x).hasDerivAt
 have h':(fun i=> (G i).det*w^2) =ᶠ[𝓝 x] fun i=> W i^2:=by
    filter_upwards [H,hP] with i h p; have hx:(B i)ᵀ= -(B i):=body_skew p h; have hh:=strata U s H.self_of_nhds hx (show IsUnit (stage (twist U (cutM s)) (C x)) from hs ▸ Hp); change (G i).det*w^2=W i^2; exact (congrArg (fun z:Op I=> Matrix.det (relay z (C x) (B i))*w^2) hs).trans hh.symm
 have hm:=((hS.pow 2).congr_of_eventuallyEq h').unique (hl.mul_const (w^2)); rw [hp,pow_one] at hm; have he:w'=qv*w:=by
    apply mul_right_cancel₀ hf; change w'*w=S.trace/2*w*w; push_cast at hm; linear_combination hm/2 -- tune
 have hn: acts L A'= qv • (A x):=by
    have hw':= ((acts L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hd; change HasDerivAt (fun t=>acts L (A t)) _ x at hw'; rw [h₀]; change acts L A'=qv • w • Z; rw [smul_smul,←he]; exact hw'.unique ((hS.smul_const Z).congr_of_eventuallyEq ha)
 exact hd.congr_deriv (hg.trans (congr_arg (HAdd.hAdd (acts (dg J) (A x))) hn))
end YM.CF.Fock.Celeb
end
