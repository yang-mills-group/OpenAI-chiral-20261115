import YM.SU5.SatinWard.Resolution.CanterJ
import YM.SU5.SatinWard.Resolution.GirlF
import YM.SU5.SatinWard.Resolution.Embassy
import YM.SU5.SatinWard.Resolution.Chorister
import YM.SU5.SatinWard.Resolution.Lens
import YM.SU5.SatinWard.Resolution.Aviator
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
open ShapeLab ShapeLab.ResolutionFrame ShapeLab.SoulField
open Verdance Installment Mezzo
-- Additional possible request finances; don't try to use `T.ρ` convenience property of another Cronus
noncomputable def buoyL (d:ℝ)(X Z: TintDemand): TintDemand:=fun K L P C Γ Tξ=> let A:=Asteroid K Tξ P C Γ; X K L P C Γ Tξ+(tinyAppointment (yardF (spinFrame 3)) (assets A) (basePurchase (paidUp d Z K L P C Γ Tξ) A) 3 (stretch_funded _).choose_spec.large (assets_own _).1 (geometryRent _ A).1).exists.choose
noncomputable abbrev wardRate (d:ℝ)(X Z:TintDemand):TintDemand:= buyPSE d (buoyL d X Z) Z
local notation "L!"=> P.par.R.L
local notation "Cc"=>yardF (spinFrame 3)
local notation "K★"=>Asteroid P.par.K Tξ Pay kC Γ
variable (g:FinanceLeaf (pushGarden (wardRate td Υ extra)) (paidUp td extra) m P Tξ Pay kC Γ Z V F W n)(h:StageBooking P Tξ Pay kC Γ Z V F W m (study td P extra Tξ Pay kC Γ) td)
variable (M:P.Roster)(v0:Fintype.card (Announcement Wage3 η) ≤ m)
include v0 g h
lemma survey_fields : ∀ᶠ s in atTop,∀ v:ℕ,s≤v→∀ᶠ i in atTop,∀ k:ℕ, Satin.PairIdx P.run (v+1) i k→∃ U γ, Crescita (i:=i) (a₀:=s) (g:=v) (k:=k) P.run 3 η Α U γ:=by
 obtain ⟨a,b,c,h',hx,P0,M₁⟩:= h.available
 obtain ⟨a₁,k,h,kq,tq⟩:= pricesReq td (festive (buoyL td Υ extra)) extra m P n Tξ Pay kC Γ Z V F W g
 have t :(spinFrame 3).pulseHidden L! Cc (assets (Asteroid P.par.K Tξ Pay kC Γ)) (study td P extra Tξ Pay kC Γ)≤ stepTiny:=by
    obtain hs:= g.shines.2.2.2.2.1; unfold pushGarden wardRate buyPSE greenBill festive buoyL at hs; dsimp only at hs; refine (tinyAppointment Cc ℌ (basePurchase (paidUp td extra P.par.K P.par.L Pay kC Γ Tξ) (Asteroid P.par.K Tξ Pay kC Γ)) 3 (stretch_funded _).choose_spec.large k a₁).exists.choose_spec L! (by omega)
 have he:(Fintype.card Wage3:ℝ)*stepTiny≤1/2:=by change markCount*_≤_; linarith only [step_b,tiny_w]
 refine (M₁ 3).report η stepTiny stepTiny_pos he|>.mono fun s u i v => (u i v).mono fun j x k vk=> bumpSpiral _ _ _ _ _ _ _ _ _ _ _ _ vk (x k vk) (tq 3) t h v v0 -- order tune
structure Exposure (f0:ℕ) : Prop where
 voices(v:ℕ): f0≤v→∀ i k,v≤P.run.uv k→∀ g: UNI SU.Slot,Mezzo.Concert g→ClockSong P.run v i k g
 scale(v:ℕ): f0≤v→∀ i k,v<P.run.uv k→∀ g:UNI SU.Slot,Registrar g→twist g (((P.run.voyage i).X (P.run.uv k)).wave v).val= (((P.run.voyage i).X (P.run.uv k)).wave v).val
omit v0 h
include M
lemma expose : ∀ᶠ f0:ℕ in atTop, Exposure P f0:= by
 obtain ⟨p,h,t,y,D₁,D₂,p,q,v⟩:= g.shines
 filter_upwards [eventually_forall_ge_atTop.mpr (exactly_flavor P.run (RateCover.includes _ _ _ v) M.prepared)] with i w using ⟨fun y v j k h g=> (w y v j k h).1 g, fun y v j k p g=> (w y v j k p.le).2 p g⟩
omit M g
local notation "Θ"=> Nomina
local notation "UP" => ShapeLab.ResolutionFrame.upright
local notation "EΧ"=> CoinSong
abbrev orchestraDose (P:Spine)(A: ℝ):ℝ:= (spinFrame 3).pulseBase P.par.R.L
structure Allegory (P:Spine)(η:Type)[Fintype η](A:ℝ)(f0 g:ℕ)(X:CoinSong)(f d:ℕ→ℕ)(U:ℕ→ CoinSong) : Prop where
 eligible : ∃ γ:ℝ, Nomina γ ShapeLab.ResolutionFrame.upright (X: Talent) P.par.R.L
 visit : Tendsto U atTop (𝓝 X)
 route : StrictMono d
 funded : ∀ᶠ i:ℕ in atTop, ∃ γ:ℝ,Crescita (a₀:=f0) (g:=g) (i:=P.nomadic (f (d i))) (k:=P.engine (f (d i))) P.run 3 η A (U i:Talent) γ
private theorem issueBall (F:EΧ)(γ:ℝ)(p:Nomina γ ShapeLab.ResolutionFrame.upright (F:Talent) L!): ‖F‖ ≤ orchestraDose P 0:= ContinuousLinearMap.opNorm_le_bound F (div_pos receipt_pos ((spinFrame 3).chi_pos L!)).le (fun x=> Nomina.guide 3 ⟨p.1,p.2.1,(p.2.2).raises quarterStep⟩ x)
private theorem keeps (X:ℕ→ℝ×CoinSong)(x:ℝ×CoinSong)(h:Tendsto X atTop (𝓝 x))(t:∀ i, Nomina (X i).1 ShapeLab.ResolutionFrame.upright ((X i).2:Talent) L!): Nomina x.1 ShapeLab.ResolutionFrame.upright (x.2:Talent) L!:=by
 have ht:= continuous_fst.continuousAt.tendsto.comp h; have hp:Tendsto (fun i=> |(X i).1|) atTop (𝓝 |x.1|):= continuous_abs.continuousAt.tendsto.comp ht
 refine ⟨ge_of_tendsto hp (Eventually.of_forall fun i=> (t i).1), le_of_tendsto hp (Eventually.of_forall fun i=> (t i).2.1), fun i=>?_⟩; let q(w:ℝ×CoinSong):= ‖w.1 • (w.2 i)-i‖; exact le_of_tendsto ((show Continuous q from by unfold q; exact ((continuous_fst.smul (Continuous.clm_apply continuous_snd continuous_const)).sub continuous_const).norm).continuousAt.tendsto.comp h) (Eventually.of_forall fun y=> (t y).2.2 i)

structure Melodic (P:Spine) (η:Type)[Fintype η](A:ℝ)(v:ℕ)(f:ℕ→ℕ) : Prop where
 initial: Exposure P v
 costs(h:ℕ): v≤h→∃ X d U, Allegory P η A v h X f d U
include M g h p v0
theorem story_fields : ∀ᶠ s in atTop, Melodic P η (study td P extra Tξ Pay kC Γ) s f :=by
 filter_upwards [survey_fields P td Pay Γ kC Tξ Z V F W Υ extra η g h v0, expose P td Pay Γ kC Tξ Z V F W Υ extra g M] with s U Q
 refine ⟨Q,fun v u=>?_⟩
 let Sv(x:ℕ)(z:ℝ×CoinSong): Prop:= Crescita (a₀:=s) (g:=v) (i:=P.nomadic (f x)) (k:=P.engine (f x)) P.run 3 η (study td P extra Tξ Pay kC Γ) z.2.toLinearMap z.1
 let W':ℝ:= roofL L! + orchestraDose P 0; have h1:= floorL_pos L!; have hx:=roofL_pos L!; have hD :0≤ orchestraDose P 0:= (div_pos receipt_pos ((spinFrame 3).chi_pos _)).le; let S':=Metric.closedBall (0:ℝ×CoinSong) W'; have hv:∀ᶠ i in atTop,∃ x∈S', Sv i x:=by
    filter_upwards [ (P.stockGo.comp p).eventually (U v u), p.eventually (marches P (v+1))] with i K E
    obtain ⟨H,b,hb⟩:= K _ E; let X:= H.toContinuousLinearMap; let z:ℝ×CoinSong:= (b,X); let ht:= hb.bumper.traceK; refine ⟨z, Metric.mem_closedBall.mpr ?_, hb⟩
    rw [dist_zero_right,Prod.norm_def]; exact max_le ((show ‖b‖ ≤ roofL L! from ht.2.1).trans (le_add_of_nonneg_right hD)) ((issueBall P X b ht).trans (le_add_of_nonneg_left hx.le))
 obtain ⟨b,q⟩:= eventually_atTop.mp hv; let Y(n:ℕ):=(q (n+b) (by omega)).choose; have hB(i): Y i∈S'∧ Sv (i+b) (Y i):=(q (i+b) (by omega)).choose_spec
 obtain ⟨c,h,R,r,v⟩:= (isCompact_closedBall _ W').tendsto_subseq (fun i=>(hB i).1); refine ⟨c.2,(fun i=>R i+b),(fun i=>(Y (R i)).2),⟨_,keeps P _ _ v fun i=>(hB (R i)).2.bumper.traceK⟩,continuous_snd.continuousAt.tendsto.comp v,(fun i j w=>by exact Nat.add_lt_add_right (r w) b), Eventually.of_forall (fun i=>⟨(Y (R i)).1, (hB _).2⟩)⟩
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
