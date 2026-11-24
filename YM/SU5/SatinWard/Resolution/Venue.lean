import YM.SU5.SatinWard.Resolution.Polaris
import YM.SU5.SatinWard.Resolution.LordWeek
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
open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace Internal Dovetail
namespace Polaris
variable (pv:skit)(ℓ:ℝ)(i:Axis)
lemma order_lag(a:straight i ℓ pv): ∀ᶠ z in 𝓝 pv,straight i ℓ z:=by
 let h: Continuous (fun p:skit=> p true i-p false i):=by fun_prop
 exact h.continuousAt.tendsto.eventually (lt_mem_nhds (show 2*ℓ <_ from a))
-- order of each axis plenum varies.Leave signs.All eventually.
lemma broad_open(a:broadV ℓ pv):∀ᶠ z in 𝓝 pv,broadV ℓ z:=by
 unfold broadV; refine eventually_all.mpr (fun i=>?_); let h:Continuous (fun p:skit=>|p false i-p true i|):=by fun_prop
 exact h.continuousAt.tendsto.eventually (lt_mem_nhds (a i))
local notation "R"=> ac2
local notation "r"=> ac2.s
-- Pose points.Curve.Port.Availability.
def ript(p:skit):skit:= fun i=> ac2.s.act (p i)
lemma ript_cash : Continuous ript:=by
 refine continuous_pi (fun i=>continuous_pi fun a=>?_); obtain ⟨j,rfl⟩:= ac2.s.perm.surjective a; unfold ript; simp only [Signed.act_at]; split_ifs<;> fun_prop
-- tilt.Clock.Result at same axis. for mean
local notation "ν"=> P.sidesPerTick
local notation "ZΩ"=> P.ground
local notation "K★"=> homeTag P rayPost
local notation "Δ" v:max=> home P rayPost v
local notation "σ" v:max=> P.macroStep v
noncomputable abbrev landingY (v:ℕ)(u:Bool→ Cover):skit:= fun i=> home P rayPost v+ P.laysM (P.vtile v (u i))
abbrev qualifier (u:ℝ)(p:skit):Prop:= straight 3 u p ∧ broadV u p
lemma qual_open(h:qualifier ℓ pv): ∀ᶠ z in 𝓝 pv, qualifier ℓ z:= (order_lag _ _ _ h.1).and (broad_open _ _ h.2)
lemma turn_landing (v:ℕ)(y:Bool→ Cover): landingY P v (fun i=> ac2.s.act (y i))= ript (landingY P v y):=by
 have H(y:Cover): ac2.s.act (geoAt P v y)= geoAt P v (ac2.s.act y):=by
    funext i; obtain ⟨j,rfl⟩:= ac2.s.perm.surjective i; unfold geoAt gaugePosition; rw [Signed.act_at]; simp only [Signed.act_at]; split_ifs <;> (push_cast; ring)
 funext i; change Δ v+P.laysM (P.vtile v (ac2.s.act (y i))) = ac2.s.act (_); unfold landingY home; rw [←geo_pose,←geo_pose,H, actPost]
-- use actual independent FLOOR placements.Separation qualification also all needed.Width extra. Ridge any eventual.
noncomputable def pointTick (v:ℕ)(x: Vantage) (a:Axis):ℤ:=Int.floor ((x a-home P rayPost v a)/ σ v)
noncomputable def tideMark (v:ℕ): Bool→ Cover:=fun b=> pointTick P v (pv b) -- order
private lemma tolerance (u t:ℝ)(w:0<t): |u- Int.floor (u/t)*t|≤ t:=by
 let z:=Int.floor (u/t); have h:(z:ℝ)≤u/t:= Int.floor_le _; have h':u/t<(z:ℝ)+1:= Int.lt_floor_add_one _; rw [div_lt_iff₀ w] at h'; rw [le_div_iff₀ w] at h; change |u-z*t|≤ _; rw [abs_le]; constructor<;> linarith only [h,h',w]
local notation "bμ" n:max=> tideMark P pv n
lemma tide_gap (b:Bool)(v:ℕ):|pv b i-landingY P v (bμ v) b i| ≤ σ v:=by
 change |pv b i-(home P rayPost v i+ P.tock v (pointTick P v (pv b) i))|≤ _; rw [P.tock_price,←sub_sub]; exact tolerance _ _ (P.macroStep_pos _)
lemma tide_in : Tendsto (fun v:ℕ=> landingY P v (tideMark P pv v)) atTop (𝓝 pv):= tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr fun j=> by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ P.macroStep_zero; filter_upwards with v; rw [Real.norm_eq_abs, abs_sub_comm]; exact tide_gap P pv j i v)
-- for boxes
noncomputable def frontage(x y: Vantage):skit:= fun i=> if i then y else x
lemma front_false(u v:Vantage):frontage u v false=u:=rfl
lemma front_true(u v:Vantage):frontage u v true=v:=rfl
lemma frontAll : Continuous (fun p:Vantage × Vantage=> frontage p.1 p.2):= continuous_pi (fun i=>by cases i; exact continuous_fst; exact continuous_snd)
lemma frontSk (p:skit):frontage (p false) (p true)= p:=by funext i; cases i<;> rfl
#print axioms turn_landing
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
