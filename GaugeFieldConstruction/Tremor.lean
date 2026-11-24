import GaugeFieldConstruction.Pew
import GaugeFieldConstruction.Freizes
/-! # White window vanishing equivalence -/
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
variable {c f: Side}{G:Ratio c f}{p:Odd G.count.val}{M:Male}{A:Site f}{Q:Op (Single f)}{o:Skye.Seat f}{h:ℝ}{k m:ℕ}
def FullY (M:Male)(Q:Op (Single f))(o:Skye.Seat f)(h:ℝ)(v:Views): Pal:= fellP M false v* streamF o Q h v *fellP M true v
def Strap (M:Male)(Q:Op (Single f))(o:Skye.Seat f)(h:ℝ):PalOne := palCart (palCart (wheelP M false) (markJet o Q h)) (wheelP M true)
lemma flow_A: AptK (FullY M Q o h) (Strap M Q o h):= cart_K (cart_K (plankK M false) (K_pays o Q h)) (plankK M true)
lemma tour_W: winJ o M h Q= palCart (palCart (bladeL false) (Strap M Q o h)) (bladeL true):=by
 apply (tab M Q).unique; have hp: (fun i=> baseF false* FullY M Q o h i * baseF true)=TabX o M h Q:=funext fun i=>by rw [TabX,FullY]; simp only [mul_assoc]
 rw [← hp]; exact cart_K (cart_K (AptK.const _) (flow_A)) (AptK.const _)
lemma flow_PA {f:Views→Pal}{v:PalOne}(p:AptK f v) : AptK (fun i=> f i) v:=p
lemma wheel_idem {b:Bool}:  ∀ᶠ x in 𝓝 (0:Views), fellP M b x *fellP M b x=fellP M b x:=by -- tune binder
 cases b
 · filter_upwards [(show Tendsto (ContinuousLinearMap.fst ℝ Plane Plane) (𝓝 0) (𝓝 0) from continuousAt_fst).eventually (palP M false)] with i u; exact u.1.eq
 filter_upwards [(show Tendsto (ContinuousLinearMap.snd ℝ Plane Plane) (𝓝 0) (𝓝 0) from continuousAt_snd).eventually (palP M true)] with i u; exact u.1.eq
lemma roll_star: let U:=Strap M Q o h; palCart (wheelP M false) U= U∧ palCart U (wheelP M true)=U:=by
 intro U; let W:=FullY M Q o h
 have hp : AptK W U:=flow_A; constructor
 · apply (((cart_K (plankK M false) hp).equal ?e).unique hp); filter_upwards [wheel_idem (b:=false) (M:=M)] with i k; unfold W FullY; rw [← mul_assoc,← mul_assoc,k]
 apply (((cart_K hp (plankK M true)).equal ?_).unique hp); filter_upwards [wheel_idem (b:=true) (M:=M)] with i k; unfold W FullY; rw [mul_assoc _ _ (fellP _ _ i),k]
structure KappaF(r:ℕ)(f:PalOne):Prop where
 u : 1≤r→ f.1=0
 v : 2≤r→ f.2.1=0
 q : 3≤r→ f.2.2=0
lemma cottonZ (r:ℕ): KappaF r (winJ o M h Q) ↔ KappaF r (Strap M Q o h) := by
 let V:= Strap M Q o h; have H:=roll_star (Q:=Q) (M:=M) (o:=o) (h:=h); rw [tour_W];
 let K:=baseF false; let X:=baseF true; let S:=palCart (palCart (bladeL false) V) (bladeL true)
 change KappaF r S ↔ KappaF r V;
 have hp(i:Views): S.2.1 i=K * V.2.1 i* X:=by unfold S palCart; simp only [cart_0,cart_1]; change (0*_+K * V.2.1 i)*X+ _*0 = _; simp only [zero_mul,mul_zero,add_zero, zero_add]
 have hv(i j:Views): S.2.2.val i j= K* V.2.2.val i j* X:=by
    unfold S palCart; simp only [cart_2,cart_0,cart_1]; simp only [bladeL,Submodule.coe_zero,ContinuousLinearMap.zero_apply,zero_mul,mul_zero,add_zero,zero_add]; rfl
 obtain ⟨w,e⟩ : palCart (wheelP M false) V = V ∧ palCart V (wheelP M true)= V:= H
 have hh: S.1= V.1 :=by
    have he: K*V.1=V.1:=by unfold K; rw [← plan_o M]; exact congrArg (fun p:PalOne=>p.1) w
    have hx : V.1*X=V.1:=by unfold X; rw [← plan_o M]; exact congrArg (fun p:PalOne=>p.1) e
    change K* V.1* X= _; rw [he,hx]
 refine ⟨fun u=>?_,fun u=>?_⟩
 · have he:1≤r → V.1=0:=fun v=> hh.symm.trans (u.u v)
   have hk:2≤r → V.2.1=0:=by
      intro t; have ht:=he (by omega); apply ContinuousLinearMap.ext; intro i
      have hp' := DFunLike.congr_fun (u.v t) i; let Q':=V.2.1 i
      have hs : K * Q'=Q':=by have h:=congrArg (fun p:PalOne=> p.2.1 i) w; simp only [palCart,cart_1,ht, mul_zero,zero_add, plan_o] at h; exact h
      have hg : Q'* X=Q':=by have h:=congrArg (fun p:PalOne=> p.2.1 i) e; simp only [palCart,cart_1,ht, zero_mul, add_zero,plan_o] at h; exact h
      rw [hp] at hp'; exact (show _= _ from ((congrArg (fun i'=>i'*X) hs).trans hg)).symm.trans hp' -- tune
   refine ⟨he,hk,?_⟩; intro t; have ht:= he (by omega); have hr:=hk (by omega); apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; let V₂:= V.2.2.val i j
   have hs : K * V₂=V₂:=by have h:=congrArg (fun p:PalOne=>p.2.2.val i j) w; simp only [palCart,cart_2,ht,hr,ContinuousLinearMap.zero_apply,mul_zero,add_zero,zero_add,plan_o] at h; exact h
   have hz: V₂ * X=V₂:=by have h:=congrArg (fun p:PalOne=>p.2.2.val i j) e; simp only [palCart,cart_2,ht,hr,ContinuousLinearMap.zero_apply,zero_mul,add_zero,zero_add,plan_o] at h; exact h
   have hp:= DFunLike.congr_fun (DFunLike.congr_fun (congrArg Subtype.val (u.q t)) i) j; rw [hv] at hp; exact (((congrArg (fun i'=>i'*X) hs).trans hz)).symm.trans hp
 constructor
 · intro i; rw [hh,u.u i]
 · intro t; apply ContinuousLinearMap.ext; intro i; rw [hp i,u.v t,ContinuousLinearMap.zero_apply, mul_zero,zero_mul]
 intro t; apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; change S.2.2.val i j=(0:Pal); rw [hv,u.q t]; simp
abbrev spot{n:Side}(o:Skye.Seat n)(x:Site n):= stem (AnchorN o) x -- tune n
abbrev kNote (f:Side)(o:Skye.Seat f):Plane→L[ℝ]ℝ:= (1/2:ℝ) • rom (Layout.siteOffset o) -- namespace tune
open Layout Layout.Fren
lemma gem_v (i:Site f)(p:10*separation (node i) o < (More f).val)(u:100<f.val): stem o (node i)=2 • spot o i+ siteOffset o:=by -- category
 let A:= AnchorN o; let x:= spot o i; let H:=siteOffset o; apply lift_eq_iff.mpr; refine ⟨?_,fun j=>?_⟩
 · change node i-o=wrap _ _; have hx : parked o x=i:=by unfold parked; rw [show wrap f x=i-AnchorN o from wrap_lift _]; abel
   conv_lhs=>rw [← hx, mark_node]
   unfold spotSize; rw [add_sub_cancel_left]; unfold x; rw [add_comm]
 have hv:=delta_o i p u; let k:=separation i A; rw [separation_comm] at hv -- tune
 have hz:(H j).natAbs≤4:=(height_l ..).trans (rent_z o); have hp : (x j).natAbs≤ k:=component_le ..; change 8*k < f.val at hv
 change -( (f.val*2:ℕ):ℤ)< 2*(2*x j+ H j) ∧ 2*(2*x j+H j) ≤ ( (f.val*2:ℕ):ℤ); omega -- tune orientation strict order
lemma point_phase(x:Site f)(p:10*separation (node x) o < (More f).val)(u:100<f.val): pointF o x= kNote f o+rom (spot o x):=by
 apply ContinuousLinearMap.ext; intro y; unfold pointF kNote; rw [gem_v x p u,ContinuousLinearMap.add_apply]; simp only [_root_.smul_apply,smul_eq_mul,rom_p, Pi.add_apply, Pi.smul_apply, two_smul,Pi.add_apply]; push_cast; simp_rw [add_mul, sum_add_distrib]; ring
end Boom
end YM.CF.TableF
end
