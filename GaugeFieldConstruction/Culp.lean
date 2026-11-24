import GaugeFieldConstruction.Shiny
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
-- functions or rays
section
variable {f g u w:ℝ→ℂ}
def TierPair(f g:ℝ→ℂ):Prop:=∃ X Y Z:ℂ, TierS f X Y Z ∧ TierS g X Y Z
lemma Tpair (p:ContDiffAt ℝ 2 f 0):TierPair f f:=let x:TierS f (f 0) (deriv f 0) (deriv (deriv f) 0):=⟨p,rfl,rfl,rfl⟩; ⟨_,_,_,x,x⟩
lemma Tchain (p:TierPair f g)(q:TierPair g u):TierPair f u:=by obtain ⟨x,y,z,h,t⟩:=p; obtain ⟨w,s,r,hf,q⟩:=q; obtain ⟨rfl,rfl,rfl⟩:= t.unique hf (EventuallyEq.refl ..); exact ⟨_,_,_,h,q⟩
lemma Transe (p:TierPair f g)(q:f=ᶠ[𝓝 0] u): TierPair u g:=by obtain ⟨x,y,z,h,t⟩:=p; exact ⟨_,_,_,h.equal q,t⟩
lemma TierPair.symm (p:TierPair f g): TierPair g f:=by obtain ⟨x,y,z,h,t⟩:=p; exact ⟨_,_,_,t,h⟩
lemma add_T (p:TierPair f g)(q:TierPair u w): TierPair (f+u) (g+w):=by obtain ⟨x,y,z,h,t⟩:=p; obtain ⟨Y,Z,T,p,q⟩:=q; exact ⟨_,_,_,h.add p,t.add q⟩
lemma mul_T (p:TierPair f g)(q:TierPair u w): TierPair (f*u) (g*w):=by obtain ⟨x,y,z,h,t⟩:=p; obtain ⟨Y,Z,T,p,q⟩:=q; exact ⟨_,_,_,h.mul p,t.mul q⟩
lemma star_T(p:TierPair f g): TierPair (fun x=>star (f x)) (fun x=>star (g x)):=by obtain ⟨x,y,z,h,t⟩:=p; exact ⟨_,_,_,starTier h, starTier t⟩
lemma nil_T(p:TierS f 0 0 0): TierPair f 0:= ⟨_,_,_,p,TierS.const _⟩
lemma SumTierS {J:Type*}(S: Finset J)(v:J→ℝ→ℂ)(u:∀ i∈S,TierS (v i) 0 0 0):TierS (fun x=> ∑ i∈S,v i x) 0 0 0:=by
 let h:= TierS.sum v (fun _=>0) (fun _=>0) (fun _=>0) S u; simp only [sum_const_zero] at h; exact h.equal (Eventually.of_forall fun i=>Finset.sum_apply ..)
lemma peelT {X:Type*}(Q:Finset X)(u v:X→ℝ→ℂ)(p:∀ i∈Q,TierPair (u i) (v i)):TierPair (fun x=>∑ i∈Q,u i x) (fun x=>∑ i∈Q,v i x):=by
 classical
 induction Q using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact Tpair contDiffAt_const
 | @insert i t v ih=> simp_rw [sum_insert v]; exact add_T (p i (mem_insert_self ..)) (ih fun i v=>p _ (mem_insert_of_mem v))
lemma crumbT(p:TierS f 0 0 0)(v:ContDiffAt ℝ 2 g 0): TierS (g*f) 0 0 0:=by
 let T:TierS g _ _ _:=(show TierS g (g 0) (deriv g 0) (deriv (deriv g) 0) from ⟨v,rfl,rfl,rfl⟩)
 simpa only [mul_zero,add_zero] using T.mul p
lemma crumbT'(p:TierS f 0 0 0)(v:ContDiffAt ℝ 2 g 0): TierS (f*g) 0 0 0:=by rw [mul_comm f]; exact crumbT p v
end
variable {c f: Side} {A: Bool→ℝ} {B U' σ: ℝ}{G: Ratio c f}{M M':Male}{Q:Op (Single f)}{b:Bool}{o:Skye.Seat f}
def fanTax (G:Ratio c f)(o:Skye.Seat f)(v:Plane):= PayS (pointF (downT G o) (deckLoc G (AnchorN o))) v
variable (b) (u:Honed G.count M b B σ)(w:0<B)(t:0<σ)(e:Odd G.count.val)(x:Single f)(v:Plane)(i:Kt)
local notation "Λ"=> G.count
local notation "ρ"=> αN G.count
local notation "M₀"=> AnchorN o
local notation "Xₚ"=> μPose o x
abbrev AliTax (b:Bool)(M:Male)(G:Ratio c f)(o:Skye.Seat f)(x:Single f)(l:Site G.count)(v:Plane):= mode (aliasAt (angle v) l) (dockLoc G (AnchorN o) (μPose o x)) *Next.Free.toll G.count 2 -- prefer abbreviate
abbrev smear_P (L:Side)(b:Bool)(v:Plane)(l:Site L)(M M':Male): Pal:= bootstrap M b (aliasAt (angle v) l) * (blockX M b L l (angle v)*InputC M' b (angle v))
include u w t e
lemma LamArt (a:angle v∈ baseCube): LAM M M' G o v b x i=fanTax G o v * ∑ l:Site G.count, AliTax b M G o x l v * smear_P Λ b v l M M' (portB x) i:=by
 let A(y:Mill):= Θfull M G o b x y; let V:=fanTax G o v; unfold LAM MoonY -- tune private def
 have hp:= ontoF (angle v) b a e M₀ u w t Xₚ (portB x) i M'; rw [← show (∑' y:Mill,_)= (∑ l:Site G.count, AliTax b M G o x l v*smear_P Λ b v l M M' (portB x) i) from hp]
 rw [← tsum_mul_left]; refine tsum_congr fun j=> ?_; change PayS (measureG G o j.1) v * A j * _= _
 rw [show PayS (measureG G o j.1) v=fanTax G o v *mode (angle v) j.1 from ?_]; · unfold A Θfull; ring
 rw [← rom_e]; unfold PayS measureG fanTax; rw [_root_.add_apply,Complex.ofReal_add,mul_add,Complex.exp_add]; rfl
-- Dick Smooth smear entries: bootstrap nearby on nonprincipal Arm (alias trajectories), use h.struct `bent`.
omit u w t e
lemma αchange (z: ℝ→Plane) (p:ContDiffAt ℝ 2 z 0): ContDiffAt ℝ 2 (fun x=>angle (z x)) 0:=by
 apply contDiffAt_pi.mpr; intro i; exact Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun x=> z x i) 0 (contDiffAt_pi.mp p _)
lemma onBudget (a d:Kt): Pay (fun _:Unit=>1) (fun _=>bootstrap M b):=by
 -- use b=bool cases and expose_kron
 let H:=bent_budget b 4 (by decide) (fun _:Unit=>M.val) (fun _=>M.property); have he(x:Momentum):bootstrap M b x=Fir.bent b 4 M.val x⊗ₖ (1:Op SU.Slot):=by
    cases b; swap; rfl
    change 1-boot 4 M x=(1-Fir.bar 4 M.val x)⊗ₖ _; rw [sub_eq_add_neg 1 (Fir.bar _ _ _), Matrix.add_kronecker, Matrix.one_kronecker_one, op_kron_neg, sub_eq_add_neg] -- tune
 refine ⟨fun _=>zero_le_one,fun x y=>?_ ⟩; rcases x with ⟨q,c⟩; rcases y with ⟨s,d'⟩; simp_rw [he, Matrix.kronecker_apply]; simpa only [mul_one] using! (H.tap q s).mul (Moderate.const ((1:Op SU.Slot) c d'))
lemma sm_K (a d:Kt) : ContDiffAt ℝ 2 (fun s:ℝ=>InputC M b (angle (s • v)) a d) 0:=by
 have hh(i):ContDiffAt ℝ ω (fun s:ℝ=>bootstrap M b (angle (s • v)) a i) 0:=tap_P ((onBudget (M:=M) b a d).tap ..) () v -- tune
 unfold InputC; simp_rw [Matrix.mul_apply]; exact ContDiffAt.sum (fun i _=> ((hh i).of_le le_top).mul contDiffAt_const)
include e
lemma smear_burn(l:Site G.count)(u:l≠0)(a j:Kt):TierS (fun t:ℝ=> smear_P Λ b (t • v) l M M' a j) 0 0 0:= by
 let W(t:ℝ):=t • v; let Z(t:ℝ):=blockX M b Λ l (angle (W t)); let Q:=fun p:ℝ=>InputC M' b (angle (W p)); let Y(t:ℝ):= bootstrap M b (aliasAt (angle (W t)) l)
 have hz(x y): TierS (fun t=> Z t x y) 0 0 0:=by let C:= (1:Op SU.Slot) x.2 y.2; exact crumbT' (Nil_arm Λ M.val e M.property b v u x.1 y.1) (g:=fun _=>C) contDiffAt_const -- tune argument order
 have hp(h i:Kt): ContDiffAt ℝ 2 (fun v=> Y v h i) 0:=(tap_P (((onBudget (M:=M) b a j).on_alias (fun _:Unit=> G.count) (fun _=>e) (fun _=>l)).tap h i) () v).of_le le_top
 have hQ(x:Kt):TierS (fun t=>(Z t*Q t) x j) 0 0 0:=by simp_rw [Matrix.mul_apply]; exact SumTierS _ _ fun i _=> crumbT' (hz x i) (sm_K b v i j)
 change TierS (fun t:ℝ=> (Y t*(Z t*Q t)) a j) 0 0 0
 simp_rw [show ∀ t,(Y t*(Z t*Q t)) a j = ∑ i:Kt,Y t a i*(Z t*Q t) i j from fun t=>Matrix.mul_apply]; exact SumTierS _ _ fun i _=> crumbT (hQ i) (hp a i)
lemma smear_good (l:Site G.count)(a j:Kt):ContDiffAt ℝ 2 (fun t:ℝ=> smear_P Λ b (t • v) l M M' a j) 0:=by
 let W(t:ℝ):=t • v; let Z(t:ℝ):=blockX M b Λ l (angle (W t)); let Q:=fun p:ℝ=>InputC M' b (angle (W p)); let Y(t:ℝ):=bootstrap M b (aliasAt (angle (W t)) l)
 have hz (x y):ContDiffAt ℝ 2 (fun t=>Z t x y) 0:=((arm_K Λ M.val e M.property b v l x.1 y.1).of_le le_top).mul (contDiffAt_const (c:= (1:Op SU.Slot) x.2 y.2))
 have hp(h i:Kt): ContDiffAt ℝ 2 (fun v=> Y v h i) 0:=(tap_P (((onBudget (M:=M) b a j).on_alias (fun _:Unit=> G.count) (fun _=>e) (fun _=>l)).tap h i) () v).of_le le_top
 have hQ(x i:Kt):ContDiffAt ℝ 2 (fun t=>(Z t*Q t) x i) 0:=by simp_rw [Matrix.mul_apply]; exact ContDiffAt.sum fun j _=>(hz x j).mul (sm_K b v j i)
 change ContDiffAt ℝ 2 (fun t=> (Y t*(Z t*Q t)) a j) 0; simp_rw [show ∀ t,(Y t*(Z t*Q t)) a j = ∑ i:Kt,Y t a i*(Z t*Q t) i j from fun t=>Matrix.mul_apply]; exact ContDiffAt.sum fun i _=> (hp a i).mul (hQ i j)
lemma AliTalk (l:Site G.count):ContDiffAt ℝ 2 (fun t:ℝ=> AliTax b M G o x l (t • v)) 0:=by -- M by M binder appears context, accidental include e ok
 let f(p:Momentum):= mode (aliasAt p l) (dockLoc G M₀ Xₚ)*Next.Free.toll G.count 2
 have ht:ContDiff ℂ ω f:=by unfold f mode aliasAt; fun_prop -- tune
 have hp:ContDiffAt ℝ ω f (angle ((0:ℝ) • v)) := (ht.contDiffAt.analyticAt).restrictScalars.contDiffAt -- tune
 exact (hp.comp 0 (ray_D v)).of_le le_top
lemma fanFoot : ContDiffAt ℝ 2 (fun t:ℝ=>fanTax G o (t • v)) 0:=by
 let K:=pointF (downT G o) (deckLoc G M₀); change ContDiffAt ℝ 2 (fun t:ℝ=>PayS K (t • v)) 0
 simpa only [mul_one] using! ( (factor_sale K (1:ℂ)).turn v).cost
include u w t
lemma Lam_Pr : TierPair (fun t:ℝ=>LAM M M' G o (t • v) b x i) (fun t:ℝ=>fanTax G o (t • v)*(AliTax b M G o x 0 (t • v) * smear_P Λ b (t • v) 0 M M' (portB x) i)):=by
 let F(l:Site G.count)(t:ℝ) := AliTax b M G o x l (t • v)* smear_P Λ b (t • v) l M M' (portB x) i
 have he :TierPair (fun t=> ∑ l:Site G.count, F l t) (F 0):=by
    let A(l:Site G.count)(t:ℝ):= if l=0 then F l t else 0
    rw [show F 0=fun v=>∑ l:Site G.count,A l v from (by funext i; simp [A])]; apply peelT; intro k _
    by_cases h:k=0; · rw [show A k=F k from funext fun i=> if_pos h]; exact Tpair ((AliTalk (M:=M) b e x v k).mul (smear_good b e v k _ _))
    rw [show A k=0 from funext fun i=> if_neg h]; exact nil_T (crumbT (smear_burn b e v k h _ _) (AliTalk b e x v k))
 refine Transe (mul_T (Tpair (fanFoot (o:=o) e v)) he) ?_
 let D:= fun t:ℝ=> t • v; have hz:Tendsto D (𝓝 0) (𝓝 0):=(show Continuous (fun t:ℝ=> t • v) from by fun_prop).tendsto' 0 0 (zero_smul ..)
 exact (hz.eventually buoy_l).mono fun i' h=> (LamArt (G:=G) b u w t e x (D i') i h).symm -- tune
end Boom
end YM.CF.TableF
end
