import GaugeFieldConstruction.MeterΛ
import GaugeFieldConstruction.GlitchFe
import GaugeFieldConstruction.PartyD
import GaugeFieldConstruction.GravelFe
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
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
open BrentFe
open YM.GaugeFieldConstruction Flavor -- potential namespace collision
open BluffV BluffV.Fables
variable (g:Flavor)

lemma clanCur (x:Matter.Slot) : sensor (1:Flavor) x=x:=by rw [sensor,Pi.one_apply,leg_one]
lemma clanComp (h:Flavor)(x: Matter.Slot):sensor (g*h) x=sensor g (sensor h x):=by simp [sensor,leg_mul]
def clanPerm : Equiv.Perm Matter.Slot where
 toFun:=sensor g
 invFun:=sensor g⁻¹
 left_inv:=fun i=> by rw [←clanComp,inv_mul_cancel,clanCur]
 right_inv:=fun i=>by rw [←clanComp,mul_inv_cancel,clanCur]
lemma clanInk (x y:Matter.Slot): (δΔFe g).val x y= if sensor g y=x then pay (sensation g y) (1:ℂ) else 0:=by
 change player (ΨsFe _) x y= _; rw[player_v]; change (if _ then chipFe _ _ _ else _) =_; rw [chipFe_v]; -- tune
 obtain ⟨i,a⟩:=x; obtain ⟨j,b'⟩:=y
 by_cases h:a=b'<;> simp [sensor,sensation,h,eq_comm]
lemma chipMulFe (h:GaugeFieldConstruction.proper3)(a:GaugeFieldConstruction.proper3):chipFe (h*a)=chipFe h*chipFe a:=by
 ext i j; rw [Matrix.mul_apply,sum_eq_single (Flavor.leg a j)]
 · simp only [chipFe_v,Flavor.leg_mul,Flavor.mark_mul,ite_true]; by_cases p:Flavor.leg h (Flavor.leg a j)=i <;> cases Flavor.mark h (Flavor.leg a j) <;> cases Flavor.mark a j<;> simp [p]
 · intro z u v; rw [chipFe_v a,if_neg (Ne.symm v),mul_zero]
 simp
lemma chipMulU(h:Flavor):chipUFe (g*h)=chipUFe g*chipUFe h:=funext fun i=> Subtype.ext (chipMulFe _ _)
lemma Fee_mulfe (b:Bool)(z:ℂ): pay b (1:ℂ)*z= pay b z:=by cases b<;>simp
lemma ilkFe (I:Type*)[Fintype I][DecidableEq I](x y:I×Matter.Slot): (RiseFe I (chipUFe g)).val x y= if (y.1,sensor g y.2)= x then pay (sensation g y.2) (1:ℂ) else 0:=by
 change ( (1:Op I)⊗ₖ (δΔFe g).val) x y= _; obtain ⟨i,r⟩:=x; obtain ⟨j,s⟩:=y; rw [Matrix.kronecker_apply,clanInk]; by_cases h:i=j<;> simp [Matrix.one_apply,h,Ne.symm]
abbrev clanVFe(n:Side):Equiv.Perm (Tulip.Single n):= Equiv.prodCongr (Equiv.refl _) (clanPerm g)
abbrev clanWFe(n:Side): Equiv.Perm (Wa n):= Equiv.optionCongr (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (clanVFe g n) (clanVFe g n)))
def tollFe(z:Wa n):Bool:=z.elim false fun i=> (sensation g i.2.1.2).xor (sensation g i.2.2.2)
lemma babeFe (i:Bool) : moko (TVfe n g) false i=(TVfe n g).val:=by
 cases i; · exact seal_fe ..
 rfl
lemma boostFe (x y:Wa n): boostX (TVfe n g) false x y= if clanWFe g n x=y then pay (tollFe g x) (1:ℂ) else 0:=by
 rcases x with _|⟨b,h,t⟩ <;> rcases y with _|⟨c,j,k⟩
 · simp [tollFe,boostX,clanWFe]
 · simp [boostX,clanWFe]
 · simp [boostX,clanWFe]
 simp only [boostX,Bool.xor_false]; rw [babeFe,babeFe,ilkFe,ilkFe]; change (if b=c then (if clanVFe g n h=j then _ else _) * (if clanVFe g n t=k then _ else _) else _)=(if some (b,clanVFe g n h,clanVFe g n t)=some _ then _ else _); simp only [Option.some.injEq, Prod.mk.injEq]; unfold tollFe; split_ifs with v e T
 all_goals cases z:sensation g h.2 <;> cases q:sensation g t.2 <;> simp_all

lemma carrierQ (x:Wa n)(V:Paper n)(U: Pane n): TribePFe g V (clanWFe g n x) U = pay (tollFe g x) (V x U):=by
 unfold TribePFe CardCraft; rw [stripeQ]; simp_rw [boostFe]; simp only [Equiv.apply_eq_iff_eq]; rw [sum_eq_single x,if_pos rfl]; change pay _ (1:ℂ)*V x U=_; rw [Fee_mulfe]
 · intro y _ u; rw [if_neg u,zero_mul]
 simp
lemma τPFe_C(x y:Paper n): TribePFe g (x+y)=TribePFe g x+TribePFe g y:=funext fun i=>funext fun j=>congrFun (oneCκ (αLines x _) (αLines y _) _ _ _) i
lemma τPFe_H(x:Paper n)(c:ℂ):TribePFe g (c • x)=c • TribePFe g x:=funext fun i=>funext fun j=>congrFun (scaleCκ (αLines x _) _ _ _ _) i
def TribeLFe(n:Side): Paper n→ₗ[ℂ] Paper n where
 toFun:= TribePFe g
 map_add':=τPFe_C g
 map_smul':=fun a b=> τPFe_H g b a
lemma Tribe_fe_sum {I:Type}(f:I→Paper n)(T:Finset I):TribePFe g (∑ i∈T,f i)=∑ i∈T, TribePFe g (f i):=map_sum (TribeLFe g n) _ _
lemma plac_fe (F H:hart_X n)(h:∀ x:Pane n,H x=twist (TVfe n g) (F x)): plac H true=TribePFe g (plac F true):=by
 funext i A; let U:=TVfe n g; let P:=F A
 rcases i with _|⟨b,c,d⟩; · rfl
 have hx(t:Bool):sealC (αLines (plac F true) A) t= if t then P else 0:=by cases t <;>ext i j<;>rfl
 cases b
 · have hp:=seal_D U false false (αLines (plac F true) A) false; rw [hx] at hp; change sealC _ false=moko _ _ _ * (0:Op (Single n))* _ at hp; rw [mul_zero,zero_mul] at hp; exact Matrix.ext_iff.mpr hp.symm c d
 have hp:=seal_D U false false (αLines (plac F true) A) true; rw [hx] at hp; change sealC _ true=twist U P at hp; rw [← h] at hp; exact Matrix.ext_iff.mpr hp.symm c d
#check GuideFe
#print axioms GuideFe
lemma Herb_fe(o:Skye.Seat n)(t:20<n.val)(u:0<h)(x:p.power≤3)(l:p.order≤6)(V: Waves):Bush o M p h (SpinFe (chipUFe g) V)=TribePFe g (Bush o M p h V):=by
 let Y:= SpinFe (chipUFe g) V; let L:=αPureX o M p V; let W:= αGuide o M p V h
 have ht:Silex (CoverP o (bF4 V).val (bF5 V) p)=TribePFe g (Silex (CoverP o (bF4 V).val (bF5 V) p)):=by
    let Z:= CoverP o (bF4 V).val (bF5 V) p; funext i y; rcases i with _|⟨a,t,u⟩; · rfl
    unfold TribePFe CardCraft; rw [stripeQ,Fintype.sum_option]; simp only [boostX,zero_mul,zero_add]; simp [αLines,Silex,isolate,cSignX] -- tune
 unfold Bush; rw [τPFe_C, τPFe_C]; apply congrArg₂ (· + ·) ht; apply congrArg₂ (· + ·) <;> (first| unfold busF Pyl| unfold busG); all_goals rw [Tribe_fe_sum]; apply sum_congr rfl; intro i _
 · apply plac_fe; intro A; rw [αPureFe]; exact beamFe ..
 apply plac_fe; intro A; rw [GuideFe o _ M t u x l,malletFe]; exact beamFe ..
lemma Moon_fe(o:Skye.Seat n)(t:20<n.val)(u:0<h)(x:p.power≤3)(l:p.order≤6)(V:Waves):bushMoon M o p h (SpinFe (chipUFe g) V)=TribePFe g (bushMoon M o p h V):=by
 unfold bushMoon; rw [τPFe_H,Tribe_fe_sum]; apply congrArg; apply sum_congr rfl; intro i _; rw [CurveS,CurveS,MasonFe, Herb_fe M g _ t u x l, Signet_barFe]
end YM.CF.XGarden.MastTin.ArtCart
end
