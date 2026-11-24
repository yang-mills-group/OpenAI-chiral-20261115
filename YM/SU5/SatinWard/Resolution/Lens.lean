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
variable (g:FinanceLeaf (pushGarden (Installment.greenBill td Υ extra)) (paidUp td extra) m P Tξ Pay kC Γ Z V F W n)(h:StageBooking P Tξ Pay kC Γ Z V F W m (study td P extra Tξ Pay kC Γ) td)
structure CriticalClock (C H A:ℝ)(g f0:ℕ) (η:Type)[Fintype η] (q: Bool→ Coords Wage4) (ν:ℕ → ℕ) (f:ℕ→ℕ) (X:ℕ→ Bool → Coords Wage4): Prop where
 growth :mBooster P.par.R.L (portGain q)
 limit : Tendsto X atTop (𝓝 q)
 earned :∀ᶠ i in atTop,Confirmed η P.run A C H f0 g (P.nomadic (f (ν i))) (P.engine (f (ν i))) (X i)
 visits :StrictMono ν
 paid :∀ j, ‖q j‖ ≤ vboost P.par.R.L C H A
-- mention calendar.Fee.OUT. earnings
structure Calendrical (C H A:ℝ)(f0:ℕ)(η:Type)[Fintype η](f:ℕ→ℕ): Prop where
 fiscal : 1≤ C ∧ 1≤ H ∧ 1≤A∧PantryFin Wage4 cloverFrame P.par.R.L A C H
 stock :∀ j:ℕ,f0≤j → (0 <lapQ P.run j ∧ lapQ P.run j ≤ 1) ∧ payable P j 2
 enough:∀ g:ℕ, f0≤g → ∃ q ν X, CriticalClock P C H A g f0 η q ν f X

lemma marches (s:ℕ): ∀ᶠ i in atTop, Satin.PairIdx P.run s (P.nomadic i) (P.engine i):=(P.history.finance (s+1)).mono fun i p=>⟨p.depth,p.enters⟩
private lemma closed_hull {C H A:ℝ}{P:Spine}{q:Bool→ Coords Wage4}{x:ℕ→ Bool→ Coords Wage4} (t:Tendsto x atTop (𝓝 q))(h:∀ᶠ i in atTop, mBooster P.par.R.L (portGain (x i))∧∀ j, ‖x i j‖ ≤ vboost P.par.R.L C H A): mBooster P.par.R.L (portGain q)∧∀ j, ‖q j‖≤vboost P.par.R.L C H A:=by
 let w(c:Bool→ Coords Wage4):= |portGain c|; have hp:Continuous w:=by unfold w portGain; simp_rw [gather_formula]; fun_prop -- elab
 have D :Tendsto (fun i=>w (x i)) atTop (𝓝 (w q)):= hp.continuousAt.tendsto.comp t
 exact ⟨⟨ge_of_tendsto D (h.mono fun _ i=> i.1.1),le_of_tendsto D (h.mono fun _ i=>i.1.2)⟩,fun j=> le_of_tendsto ((tendsto_pi_nhds.mp t j).norm) (h.mono fun _ i=>i.2 j)⟩ -- i.1.1 def reducible?
include p g h μ
lemma calendar : ∀ᶠ s in atTop,Calendrical P (yardF cloverFrame) (assets (Asteroid P.par.K Tξ Pay kC Γ)) (study td P extra Tξ Pay kC Γ) s η f:=by
 obtain ⟨a,b,c,h',M,x,H⟩:=h.available; obtain ⟨fa,fh,Lg,fp,_⟩:= Installment.pricesReq td Υ extra m P n Tξ Pay kC Γ Z V F W g
 let ε:=(1:ℝ)/(2*(1+Fintype.card Wage4)); let L:=P.par.R.L
 have zt: (Fintype.card Wage4:ℝ)*ε ≤ 1/2:=by
    unfold ε; rw [←mul_div_assoc]; apply (div_le_iff₀ (by positivity : (0:ℝ)< 2*(1+Fintype.card Wage4))).mpr; linarith
 have px: ∀ᶠ s:ℕ in atTop,payable P s 2:= eventuallyPay P 2
 let D:= vboost L 𝐶 ℌ Α
 filter_upwards [eventually_forall_ge_atTop.mpr (P.slotlate.and px), x.report η ε (by unfold ε; positivity) zt] with s v z
 refine ⟨⟨(stretch_funded _).choose_spec.large,fh, fa,fp⟩, fun j u=> (v j u),fun k hk=>?_⟩ -- ↔ check
 let G(x:ℕ)(q):= Confirmed η P.run Α 𝐶 ℌ s k (P.nomadic (f x)) (P.engine (f x)) q
 let S' := Metric.closedBall (0:Bool→ Coords Wage4) D
 have hp: ∀ᶠ i in atTop, ∃ x∈ S', G i x:=by
    filter_upwards [(P.stockGo.comp p).eventually (z k hk), p.eventually (marches P (k+1))] with i s v
    obtain ⟨X,Fx⟩:= perks P.run Γ m Z V F W _ _ _ _ hk (s _ v) fp Lg v μ; have h':0 ≤ D:=(norm_nonneg _).trans (Fx.board.rimBound true); refine ⟨X, ?_, Fx⟩; apply Metric.mem_closedBall.mpr; rw [dist_zero_right]; exact pi_norm_le_iff_of_nonneg h' |>.mpr Fx.board.rimBound
 obtain ⟨i,p₀⟩:= eventually_atTop.mp hp -- not choose
 let X(n:ℕ): Bool→ Coords Wage4:= (p₀ (n+i) (by omega)).choose
 have Xq(n:ℕ): X n∈S' ∧ G (n+i) (X n):= (p₀ (n+i) (by omega)).choose_spec
 obtain ⟨q,tq,R,MR,v⟩:= (isCompact_closedBall _ D).tendsto_subseq (fun i=> (Xq i).1);
 have D':=Eventually.of_forall (f:=atTop) fun i=> (Xq (R i)).2; obtain ⟨ph,d'⟩:=closed_hull (P:=P) v (D'.mono fun i y=>⟨y.board.limit,y.board.rimBound⟩); exact ⟨q,fun n=>R n+i,X∘R,ph,v,D',fun a b h=> by exact Nat.add_lt_add_right (MR h) _,d'⟩ -- need MR h
 -- hole px
#print axioms calendar
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
