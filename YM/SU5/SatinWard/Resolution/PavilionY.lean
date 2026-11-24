import YM.SU5.SatinWard.Resolution.Lens
import YM.SU5.SatinWard.Resolution.Liaison
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
variable {m n:ℕ}(td Pay Γ kC:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(Z V F W:ℝ→ℝ)
variable {f:ℕ→ℕ}(p:Tendsto f atTop atTop)
variable (Υ extra: TintDemand) (η:Type)[Fintype η][DecidableEq η](μ: Fintype.card (Announcement Wage4 η)≤ m)
local notation "Ζ★"=>Asteroid P.par.K Tξ Pay kC Γ
local notation "𝐶" => yardF cloverFrame
local notation "ℌ"=> assets (Ζ★)
local notation "Α" =>study td P extra Tξ Pay kC Γ
variable (g:FinanceLeaf (pushGarden (Installment.greenBill td Υ extra)) (paidUp td extra) m P Tξ Pay kC Γ Z V F W n)(h:StageBooking P Tξ Pay kC Γ Z V F W m (study td P extra Tξ Pay kC Γ) td)
open Harmonic RecruitW LitCurrent LitCurrent.Chamber
variable (M₁: P.Roster) (M₂:Solstitial P.par)(M₃:RateStamp P.run) [Nonempty η] (u:Fintype.card (Announcement Wage3 η) ≤ m)
local notation "Y"=> P.run
local notation "Dc"=> LitCurrent.Chamber.Division
variable (s v i k:ℕ){j:ℕ}{a b φ θ:ℝ}
local notation "Cc"=> yardF (spinFrame 3)
local notation "τv" v:max i:max k:max=> eraτ P.run v i k j a φ
structure Lockreef (H A:ℝ)(d:Dc)(E:eraτ P.run v i k j a φ)(Wq Ws: Coords Wage4)(WJ: Coords Wage3):Prop where
  stakeQ :ArkLease (Wage4⊕η) P.run cloverFrame i k s v A (yardF cloverFrame) H (paintClass P.run v i k) (fun x=>qField P.run E x d) Wq
  stakeS :ArkLease (Wage4⊕η) P.run cloverFrame i k s v A (yardF cloverFrame) H (paintClass P.run v i k) (fun x=>starField P.run E x d) Ws
  stakeJ :ArkLease (Wage3⊕η) P.run (spinFrame 3) i k s v A (yardF (spinFrame 3)) H (spinClass P.run v i 3) (fun x=>JField P.run E x d (3,false)) WJ
noncomputable abbrev strollϕ (B:Type)[Fintype B] :ℝ:=(1:ℝ)/(2*(1+Fintype.card B))
lemma strollCost (B:Type)[Fintype B] : 0<strollϕ B ∧ (Fintype.card B:ℝ)*strollϕ B ≤1/2:=by
 unfold strollϕ; constructor; · positivity
 rw [←mul_div_assoc]; apply (div_le_iff₀ (by positivity : (0:ℝ)< 2*(1+Fintype.card B))).mpr; linarith
include M₁ M₂ M₃ μ u g h
structure Rearward (P:Spine)(η:Type)[Fintype η](j s:ℕ)(H A a b φ:ℝ):Prop where
  flow :∀ v:ℕ,s ≤ v→∀ᶠ i in atTop,∀ k, Satin.PairIdx P.run (v+1) i k→ MaskPoint P.run j v i k a b ∧ Nonempty (eraτ P.run v i k j a φ) ∧ ∀ (d:Dc)(E:eraτ P.run v i k j a φ),∃ Q S J, Lockreef P η s v i k H A d E Q S J
lemma starRise (j:ℕ) : ∃ a b φ:ℝ,0<a∧0<b∧ 0<φ ∧∀ᶠ s in atTop,Rearward P η j s ℌ Α a b φ:=by
 obtain ⟨aL,bL,cL,hL,hB,L₀,L₁⟩:= h.available; obtain ⟨a,b,ha,hb,hp⟩:= leaseFrame Y M₁.prepared M₃ M₂ j
 obtain ⟨φ,tφ,hx⟩:= LitCurrent.plan_code j ha hb P.par.d
 obtain ⟨t,ht,hq,tQ⟩:= boxPurchase (b:=b) (v:=φ) (j:=j) Y ha; obtain ⟨vs,vs',vJ,vJ'⟩:=crateLock P.par Y j a b φ ha; obtain ⟨fa,fh,Lg,fp,fS⟩:= Installment.pricesReq td Υ extra m P n Tξ Pay kC Γ Z V F W g; have hz:=g.shines
 let H0{ι:Type}[Fintype ι][DecidableEq ι](U:ResolutionFrame ι)(M:(i k s:ℕ)→ι→ Site (side Y i s)→Mark (side Y i s))(e:Directory P Γ Α ℌ aL bL cL td m Z V F W (Ζ★) U M)(p':Fintype.card (Announcement ι η) ≤ m)(p₀:PantryFin ι U P.par.R.L Α (yardF U) ℌ)(B G':ℝ→ℝ)(hB:Chill_v B)(ht:Chill_v G'):= RecruitW.enter Y Γ Pay kC Tξ n m Z V F W g.order g.Jade M₁.prepared U (yardF U) ℌ Α M hz.2.2.1 hz.2.2.2.1 p' B G' hL p₀ (stretch_funded U).choose_spec Lg (e.report η (strollϕ ι) (strollCost _).1 (strollCost _).2) fh fa ht hB -- order error
 let L := ℌ; let Q:=H0 _ _ L₀ μ fp _ _ hq ht; let S:= H0 _ _ L₀ μ fp _ _ vs vs'; let J:= H0 _ _ (L₁ 3) u (fS 3) _ _ vJ' vJ
 refine ⟨a,b,φ,ha,hb,tφ,?_⟩
 filter_upwards [ Q,S,J,eventually_forall_ge_atTop.mpr ((hp.and (P.slotlate)).and tQ)] with s vq vS vJ hv
 refine ⟨fun v h=>?_⟩; obtain ⟨⟨ho, t⟩,tc⟩:= hv _ h
 filter_upwards [vq _ h,vS _ h,vJ _ h,tc] with i K' S' J' β k f0
 have w:v< P.run.uv k:=(Nat.lt_succ_self _).trans f0.2; let W₀:=ho i k w
 refine ⟨W₀,hx _ _ W₀.ppm W₀.term W₀.permit, fun d pE=>?_⟩
 obtain ⟨q,HQ⟩:= K' k f0 _ (β k w W₀ pE d); obtain ⟨s',HS⟩:= S' k f0 _ (starLock Y t.1 w W₀ pE d); obtain ⟨j',pp⟩:= J' k f0 _ (beatLock Y t.1 w W₀ pE d 3); exact ⟨q,s',j',HQ,HS,pp⟩  -- inserted `Nonempty η` signature Lockreef? structures omit unused fields; check.
#print axioms starRise
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
