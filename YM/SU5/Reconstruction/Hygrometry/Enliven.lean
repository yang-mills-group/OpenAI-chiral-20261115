import YM.SU5.Reconstruction.Hygrometry.OnSite
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open PriceCliff
variable {N:Side} (x:Window.Family)(i k:Fin 2)
namespace Locomotive
-- price for REAL T pose of state here in authentic stencil. Strict on any truly-positive aperture point
variable (P:Ramp)(y:Gaia)
local notation "A"=> P.a
local notation "B"=> P.b
local notation "Δ"=> y-(land_tilt P y)
local notation "π"=>Real.pi
local notation "θ"=> y.ofLp P.a+y.ofLp P.b
local notation "κ"=> Real.sqrt 2
local notation "G"=>gammaOp A+gammaOp B
lemma totalStrike : ∑ i:Axis,((Δ).ofLp i:ℂ) • gammaOp i= (θ:ℝ) • G:=by
 rw [Windward.tot P]; have he(i:Axis): (Δ).ofLp i=y.ofLp i-P.s.act y.ofLp i:=rfl
 simp_rw [he,BZ.ofReal_action]; rw [P.move_a,P.move_b, Finset.sum_eq_zero]; swap
 · intro i hi; obtain ⟨h,u⟩:=Finset.mem_erase.mp hi; rw [P.move_h y.ofLp ((Finset.mem_erase.mp u).1) h,sub_self,zero_smul]
 rw [add_zero]; module
private lemma minLaw: minA=1-Aop:=rfl
private lemma barrier {v:Ket SpinIdx}(hv:acts Aop v=v): acts grading v=v:=by rw [Fir.ordA,act_sub,act_smul,hv,act_one]; module
private lemma desert {v:Ket SpinIdx}(hv:acts Aop v=0): acts grading v= -v:=by rw [Fir.ordA,act_sub,act_smul,hv,act_one,smul_zero,zero_sub]
private lemma reaper: P.imageP= κ⁻¹ • (G*grading):=by unfold Ramp.imageP; rw [add_mul]; rfl
private lemma offset_plus : (Aop:Op SpinIdx)*(P.imageP)= P.imageP-(P.imageP)*Aop:=by
 have he:=(whisper P).shades; change (1-Aop)*P.imageP= P.imageP*Aop at he; rw [sub_mul,one_mul] at he; exact eq_sub_of_add_eq (by abel_nf;rw [←he]; abel) -- tune
noncomputable def chargePos (P:Ramp)(y:Gaia):= (Real.pi^2*‖y-land_tilt P y‖^4)⁻¹*( (y.ofLp P.a+y.ofLp P.b)*Real.sqrt 2 )
lemma payPos (h:face_tilt P y):0<chargePos P y:=by
 have ht:0 < ‖y-land_tilt P y‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (fun e=> by have v:=congrArg (fun x:Gaia=> x A) e; change _= P.s.act _ _ at v; rw [P.move_a] at v; unfold face_tilt at h; linarith))
 have hx:0<θ:=h; unfold chargePos; positivity
private lemma pencil_pos (t:Ket SpinIdx)(h:acts Aop t=t) : acts (pencil Δ) t=(chargePos P y:ℂ) • acts P.imageP t:=by
 let p:= P.reel.val; let S:= G
 have hk: acts S t=(κ:ℂ) • acts p t:=by
    change _=(κ:ℂ) • acts P.imageP t; rw [reaper,←BZ.ofReal_action];
    rw [act_smul,act_mul,barrier h, Complex.ofReal_inv]; exact Eq.symm (smul_inv_smul₀ (show (κ:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (by positivity)) _)
 have hyv:acts minA (acts p t)=acts p t:=by rw [minLaw,act_sub,act_one,←act_mul Aop,show Aop*p=_ from offset_plus P,act_sub,act_mul,h,sub_self,sub_zero]
 rw [pencil,gleamV,totalStrike]; unfold chargePos
 rw [← BZ.ofReal_action, act_smul,act_mul, ← BZ.ofReal_action,act_smul]; change ((_ : ℝ) : ℂ) • (acts minA) (((θ:ℝ):ℂ) • acts S t)= _; rw [hk,map_smul,map_smul,hyv,smul_smul,smul_smul]; congr 1; push_cast; ring
private lemma pencil_flip : pencil (land_tilt P y-y)= -pencil Δ:=by
 rw [show land_tilt P y-y= -Δ by simp,pencil]; unfold pencil; rw [gleamV, gleamV]; simp only [WithLp.ofLp_neg,Pi.neg_apply,norm_neg, neg_smul, Complex.ofReal_neg, Finset.sum_neg_distrib,mul_neg,smul_neg]
-- Written continuation cost
private lemma first_due (q:↥(colors x)):
    poster (land_tilt P y) y ((whisper P).role (boundTag x i k q false)) (boundTag x i k q false) = -(chargePos P y:ℂ):=by
 let t:Ket SpinIdx:=basisKet (upSpin i); let s:= acts P.reel.val t; have h:‖s‖=1:=by unfold s t; rw [act_unit_norm]; simp [basisKet]
 have ht:acts Aop t=t:= Personality.here (upSpin i) false (up_half i)
 change poster _ _ _ _= _; unfold poster; simp only [boundTag, Personality.pureV, ActMark.role, impel, toward, Bool.false_eq_true,ite_false, Bool.not_false,Bool.true_eq_false,ite_true]; change inner ℂ s (acts (pencil (land_tilt P y-y)) t)= _; rw [pencil_flip,act_neg,pencil_pos P y t ht]; change inner ℂ s (-((chargePos P y:ℂ) • s))=_; rw [inner_neg_right,inner_smul_right,inner_self_eq_norm_sq_to_K,h]; simp
private lemma second_due (q:↥(colors x)):poster (land_tilt P y) y ((whisper P).role (boundTag x i k q true)) (boundTag x i k q true)= (chargePos P y:ℂ):=by
 let t:Ket SpinIdx:= basisKet (dnSpin k); let r:=acts P.imageP t; have hv:‖t‖=1:=by simp [t,basisKet]
 have ht:acts Aop t=0:= Personality.here (dnSpin k) true (show _∈payroll true from mem_compl.mpr (dn_half k))
 have he:acts Aop r=r:=by unfold r; rw [←act_mul,offset_plus,act_sub,act_mul,ht,map_zero,sub_zero]
 have hz:acts P.imageP r= -t:=by unfold r; rw [←act_mul, P.squarish,act_neg,act_one]
 unfold poster; simp only [boundTag, Personality.pureV,ActMark.role,impel,toward,ite_true,Bool.not_true,Bool.false_eq_true,ite_false]; change -inner ℂ t (acts (pencil Δ) r)=_; rw [pencil_pos P y r he,hz]; rw [smul_neg,inner_neg_right,inner_smul_right, neg_neg, inner_self_eq_norm_sq_to_K,hv]; simp
private lemma no_cost(x:Gaia)(a b:Personality): poster x x a b=0:=by simp [poster,toward,pencil] -- tune
private lemma diverseP (x y:Gaia)(a b:Personality)(p:a.color≠b.color): poster x y a b=0:=by unfold poster toward; split_ifs <;> first | tauto | simp_all [Ne.symm p]
private lemma world : (ActMark.applause false)*(ActMark.applause true)=1 := by unfold ActMark.applause; simp
lemma tenorPrice (a b:↥(colors x)):
    quantum (Sum.elim (fun _=> land_tilt P y) (fun _=> y)) (Packed (whisper P) (uncurry (boundTag x i k))) (couple (selfT a) (selfT b)) =if a=b then ((chargePos P y:ℂ)^2) else 0:=by
 let T:↥(colors x):=a; let U:=uncurry (boundTag x i k); let Z:=Packed (whisper P) U
 let w:= (whisper P).role; let F'(p:Bool)(q':Bool):= poster (land_tilt P y) y (w (U (a,p))) (U (b,q'))
 have he : ∀ {X:Type} (A₁ : X→X→ℂ) (a b c d:X), Emu.runes A₁ [a,b,c,d]= A₁ a b*A₁ c d-A₁ a c*A₁ b d+A₁ a d*A₁ b c:=by intro X A₁ a b c d; simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring
 unfold quantum couple selfT; simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append]; rw [he]
 simp only [Sum.elim_inl,Sum.elim_inr, no_cost] -- may unfold right positions via defeq? tune
 change (0:ℂ)*0-F' false false*F' true true+F' false true* F' true false= _
 have hu:F' false true=0:= if_pos rfl; rw [hu]; by_cases hx:a=b
 · subst b; rw [show F' false false=_ from first_due x i k P y a,show F' true true=_ from second_due x i k P y a,if_pos rfl]; ring
 have he:a.val≠b.val:= fun t=>hx (Subtype.ext t); rw [if_neg hx,show F' false false=0 from diverseP _ _ _ _ he]; ring
open scoped ComplexOrder
lemma concretePos : harvestCost (whisper P) (land_tilt P) (fun _:↥(colors x)×Bool=> y) (uncurry (boundTag x i k)) selfT (fun _=>1) false= ((dimf x:ℂ) * (chargePos P y:ℂ)^2):=by
 let V:=uncurry (boundTag x i k); have he (j:↥(colors x)): ActMark.royalties V (selfT j)=1:=by unfold ActMark.royalties selfT; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; exact world
 unfold harvestCost; simp_rw [Function.comp_def, tenorPrice, show ∀ a, ActMark.royalties (uncurry (boundTag x i k)) (selfT a)=1 from he]; simp [chord, colors_card]
lemma clutch (h:face_tilt P y) : 0<harvestCost (whisper P) (land_tilt P) (fun _:↥(colors x)×Bool=> y) (uncurry (boundTag x i k)) selfT (fun _=>1) false:=by
 rw [concretePos]; exact_mod_cast (show 0 < (dimf x:ℝ)*chargePos P y ^ 2 from mul_pos (by unfold dimf; split <;> norm_num) (by have h:=payPos P y h; positivity))
end Locomotive
end YM.CF.Hygrometry
