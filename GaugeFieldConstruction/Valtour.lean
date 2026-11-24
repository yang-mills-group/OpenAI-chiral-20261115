import GaugeFieldConstruction.Yogin
set_option autoImplicit false
set_option maxHeartbeats 80000
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
-- Epoch hull as quadratures. actual Shipment supports.
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
local notation "oX"=> Θk n x
abbrev RealmΦ {x:Cover}(b: Bool)(i:Single n):Prop:= aptK i∈Pach (Θk n x)∧ i∈ highSea n (!b)
def Dialat (x:Cover)(P:Op (Single n)): Prop:=∀ i j,P i j≠0→ RealmΦ (x:=x) false i∧ RealmΦ (x:=x) true j
lemma Stock (L:TrackD p (Pach (Θk n x)) h G c)(T:Tuned G)(v:Pane n): Dialat x (orbitPH (AlphaY G v)):=by
 let P (i j):=G (some (true,i,j)); let K(i j):=G (some (false,j,i)); let Z:=Pach (Θk n x)
 intro i j H; rw [(bpu_T ..).1] at H; change P i j v+ -(K i j v) ≠ 0 at H
 by_cases e:P i j=0
 · have he: K i j≠0:= fun z=> H (by simp [e,z]); let V:=L.choose_spec.1 (some (false,j,i)); obtain ⟨p,h,g⟩:= T _ he; have ht:DomainP Z (some (false,j,i)):=Classical.byContradiction fun y=> he (V.2 y); exact ⟨⟨ht.2,h⟩,⟨ht.1,p⟩⟩ -- tune ht is And not nested
 obtain ⟨p,h,g⟩:= T _ e; have ht:DomainP Z (some (true,i,j)):=Classical.byContradiction fun y=> e ((L.choose_spec.1 _).2 y); exact ⟨⟨ht.1,p⟩,⟨ht.2,h⟩⟩
include w
lemma Areal (j: Single n)(b: Bool)(p:RealmΦ (x:=x) b j):∃ i: ArcK x, AngleP n x b i=j:=by
 obtain ⟨a,t⟩:=here_H j (by omega : 24<n.val) (show aptK j∈ knotX x 24 n from p.1)
 have he: a.2.1∈plusHalf ↔ b=false:=by
    rw [←show hereF n a∈ Tset n↔ a.2.1∈plusHalf from κv _, t]
    cases b <;> constructor
    · intro _; rfl
    · intro _; exact p.2
    · intro h; exact (mem_compl.mp p.2 h).elim
    intro u; contradiction
 obtain ⟨v,h⟩:=bandE b a.2.1 he; let c: ArcK x:=(a.1,v,a.2.2); have hx:a=Mct b c:= Prod.ext rfl (Prod.ext h.symm rfl)
 exact ⟨c, (congrArg _ hx.symm).trans t⟩ -- tune
lemma Spale (P:Op (Single n))(Q:Dialat x P)(h:ℝ): markJet (Θk n x) P h= ∑ i:ArcK x,∑ j:ArcK x, mastF (Θk n x) P h (AngleP n x false i, AngleP n x true j):=by
 let O:(ArcK x × ArcK x)→yardZ (n:=n):= Prod.map (AngleP n x false) (AngleP n x true); let f:= mastF oX P h; let S:= univ.image O; have he(b:Bool): Injective (AngleP n x b):= (hereN 24 (by omega:n.val > 24)).comp (Mct_I x b)
 have hx(i j:Single n)(g:(i,j)∉ S): f (i,j)=0:=by
    have hp:P i j=0:=by
       by_contra e; obtain ⟨v,t⟩:=Areal x w i _ (Q i j e).1; obtain ⟨u,h⟩:=Areal x w j _ (Q i j e).2; exact g (mem_image.mpr ⟨(v,u),mem_univ _,Prod.ext t h⟩)
    let Z:=κviews oX i.1.1 j.1.1; unfold f mastF; rw [show hill_Z (Θk n x) P h _ _=0 from (by change (h:ℂ)^2 *_*_* P i j=0; rw [hp,mul_zero])];
    apply Prod.ext
    · rw [show (postF (bookP Z 0) (flare_one (portB i) (portB j))).1=_ from rfl]; change flare_one _ _ ((bookP Z 0).1)=0; rw [fund0,map_zero]
    apply Prod.ext; · apply ContinuousLinearMap.ext; intro x; change flare_one _ _ ((bookP Z 0).2.1 x)=0; rw [fund1,mul_zero,map_zero]
    apply Subtype.ext; apply ContinuousLinearMap.ext; intro u; apply ContinuousLinearMap.ext; intro v; change flare_one _ _ ((bookP Z 0).2.2.val u v)=0; rw [fund2,mul_zero,map_zero]
 unfold markJet; rw [show oleSum univ _=∑ i:yardZ (n:=n), f i from rfl,←sum_subset (f:=f) (subset_univ S) (fun i _ h=> hx i.1 i.2 h),show S=_ from rfl,sum_image (show Injective O from fun _ _ e=>Prod.ext (he _ (congrArg Prod.fst e)) (he _ (congrArg Prod.snd e))).injOn,Fintype.sum_prod_type]; try rfl
lemma pricesP (P:Op (Single n))(h:ℝ)(i j:ArcK x): hill_Z (Θk n x) P h (AngleP n x false i) (AngleP n x true j)= (h:ℂ)^2 * (Γpay n x i j*P (AngleP n x false i) (AngleP n x true j)):=by
 let X:= AngleP n x false i; let Y:=AngleP n x true j; have hp: Caller oX X.1.1*Caller oX Y.1.1 = Γpay n x i j:= payMort x (Mct false i) (Mct true j) w; unfold hill_Z; rw [← hp]; ring
-- S band left/right including derivatives. w shape triangular recover Z from grapes.
lemma mat_D (P:Op (Single n))(v: Dialat x P)(a b: Site n): baseF false * matPH P a b=matPH P a b∧matPH P a b* baseF true= matPH P a b:=by
 let X:=matPH P a b; have he(i j:Hove.Kt)(p:X i j≠0): i∈leadB ∧ j∉leadB:=by
    let k:Single n:=((a,i.1),i.2); let l:Single n:=((b,j.1),j.2); obtain ⟨u,h⟩:=v k l p; exact ⟨mem_filter.mpr ⟨mem_univ _,(κv _).mp u.2⟩,fun y=>mem_compl.mp (show l ∈ (Tset n)ᶜ from h.2) ((κv _).mpr (mem_filter.mp y).2)⟩
 constructor
 · rw [← leadHigh]; change cutM leadB * X = X; ext i j; unfold cutM; rw [Matrix.diagonal_mul]; by_cases e:X i j =0; simp [e]; rw [if_pos (he i j e).1, one_mul]
 rw [leadLo]; change X * cutM _ =X; ext i j; unfold cutM; rw [Matrix.mul_diagonal]; by_cases e:X i j=0; simp [e]; rw [if_pos (mem_compl.mpr (he i j e).2),mul_one]
lemma cigar (P:Op (Single n))(p:Dialat x P)(h:ℝ)(i:Views): baseF false * streamF (Θk n x) P h i=streamF (Θk n x) P h i ∧ streamF (Θk n x) P h i * baseF true=streamF (Θk n x) P h i:=by
 have he:= mat_D x w P p; rw [streamS]; constructor <;> simp only [Matrix.sum_mul,Matrix.mul_sum, Matrix.smul_mul,Matrix.mul_smul,(he _ _).1,(he _ _).2]
end YM.CF.XGarden.MastTin.ArtCart
end
