import GaugeFieldConstruction.Valtour
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
local notation "oX"=> Θk n x
include w
private lemma Alloy (P: Op (Single n))(q: Dialat x P)(h:ℝ) : let A:=baseF false; let B:=baseF true; let Z:=markJet (Θk n x) P h
 postF Z ((ContinuousLinearMap.mul ℝ Pal) A)= Z ∧ postF Z ((ContinuousLinearMap.mul ℝ Pal).flip B)=Z:=by
 intro A B Z; have he:=cigar x w P q h; exact ⟨fromJ (K_pays ..) _ fun i=> (he i).1,fromJ (K_pays ..) _ fun i=>(he i).2⟩ -- tune
lemma Servers (P:Op (Single n))(q:Dialat x P)(h:ℝ): let W:=winJ (Θk n x) M h P; let Z:=markJet (Θk n x) P h; W.1=Z.1 ∧ (W.1=0 → W.2.1= Z.2.1)∧ (W.1=0→ W.2.1=0→ W.2.2=Z.2.2):=by
 intro W Z; let a:=baseF false; let b:= baseF true; let C:=palCart (wheelP M true) (bladeL true); let F:=palCart Z C; let H:=palCart (wheelP M false) F
 have hp: C.1=b:= by unfold C palCart; rw [cart_0,plan_o]; exact (bladeSeal true).1.eq
 let p:=Alloy x w P q h; have hL:a*Z.1=Z.1:=congrArg Prod.fst p.1; have hR: Z.1*b=Z.1:=congrArg Prod.fst p.2
 have wL(i):a*Z.2.1 i=Z.2.1 i:= congrArg (fun x:PalOne=>x.2.1 i) p.1; have wR(i):Z.2.1 i*b= Z.2.1 i:=congrArg (fun x:PalOne=>x.2.1 i) p.2
 have lL(i j):a*Z.2.2.val i j= Z.2.2.val i j:=congrArg (fun x:PalOne=> x.2.2.val i j) p.1; have lR(i j):Z.2.2.val i j*b= Z.2.2.val i j:=congrArg (fun x:PalOne=> x.2.2.val i j) p.2
 have y:F.1=Z.1:= by unfold F palCart; rw [cart_0,hp,hR]
 have z:H.1=Z.1:=by unfold H palCart; rw [cart_0,y,plan_o,hL];
 have v:W.1=Z.1:=by change a*H.1=_; rw [z,hL]
 have X (e:Z.1=0): F.2.1=Z.2.1:=by
    apply ContinuousLinearMap.ext; intro i; unfold F palCart; rw [cart_1,hp,wR,e,zero_mul,add_zero] -- tune ext1 Mar
 have Y (e:Z.1=0): H.2.1=Z.2.1:=by
    apply ContinuousLinearMap.ext; intro i; unfold H palCart; rw [cart_1,y,plan_o,X e,wL,e,mul_zero,zero_add]
 have E(e:W.1=0): W.2.1= Z.2.1:= by
    apply ContinuousLinearMap.ext; intro i; let V:=v.symm.trans e; change (cartF (bladeL false) H).2.1 i=_; rw [cart_1,z,Y V]; change 0*Z.1+a* _=_; rw [zero_mul,zero_add,wL]
 refine ⟨v,E, fun r t=> ?_⟩; have V:= v.symm.trans r; have Q:= (E r).symm.trans t; have hx(i):Z.2.1 i=0:=by rw [Q]; rfl
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j
 have hh:F.2.2.val i j=Z.2.2.val i j:=by unfold F palCart; simp only [cart_2,hp,hx,V,zero_mul,add_zero,lR] <;> simp
 have ht:H.2.2.val i j=Z.2.2.val i j:=by unfold H palCart; simp only [cart_2,y,V,plan_o,X V,hx,hh,mul_zero,zero_add,add_zero]; exact lL .. 
 change (cartF (bladeL false) H).2.2.val i j=_; rw [cart_2,z,V,Y V,hx i,hx j,ht]; change _*0+a*Z.2.2.val i j + (_*0+_*0)=_; rw [lL]; simp
end YM.CF.XGarden.MastTin.ArtCart
end
