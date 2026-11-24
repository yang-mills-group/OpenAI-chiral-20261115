import YM.SU5.SatinWard.Resolution.Tableyard
import YM.SU5.SatinWard.Resolution.ViewWax
import GaugeFieldConstruction.StencilEquator
/-! Locus prices.How to book all accountable supports in the same ball. Curtains permit actual different financiations. -/
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

open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
namespace Polaris
open SatinRegistration Swatch _root_.YM.SatinWFixed _root_.YM.Boundary
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin (Each)
open Rampart Chili _root_.GarnetAct.Cut
open _root_.YM.GaugeFieldConstruction.Ember.Volumetric.FirstPackMars
open Set MeasureTheory
variable (F G:Curtain)(p:skit)(T:ℝ)
lemma dawn_one_st (b:Points 1): flightTimes b∈ east 1:= fun _ _ h=> by omega
lemma dawn_pair_st (t:0<T) (h:straight 3 T p): flightTimes (cameo p)∈east 2:=by
 intro i j h'; have x:i=0:=by omega
 have y:j=1:=by omega
 subst i j; change p false 3<p true 3; unfold straight at h; linarith only [h,t]
lemma matchCoast_st (h:0<T): Coast T p↔coastAngleSt T (cameo p):=by
 let H:=coastAngleSt T (cameo p); refine ⟨fun g=>⟨h,g.quest.1,fun i=> ?_,g.wind⟩,fun w=>⟨⟨w.2.1,fun i=>?_⟩,w.2.2.2⟩⟩; · change 2*T < |p true i- p false i|; rw [abs_sub_comm]; exact g.quest.2 i
 rw [abs_sub_comm]; exact w.2.2.1 i
abbrev openCoastSt (U:Set (Points 2))(p:skit)(d:ℝ):Prop:=∀ l∈closedBall (p false) d,∀ v∈closedBall (p true) d, cameo (frontage l v)∈ U
lemma anyCastSt (r:ℝ)(v:0<r): ∃ w y:Curtain, Rampart.Supported w y p (r/2):=by
 obtain ⟨F,xT⟩:= Curtain.grows (p false) (r/2) (half_pos v); obtain ⟨G,vT⟩:= Curtain.grows (p true) (r/2) (half_pos v); exact ⟨F,G,Eq.subset xT,Eq.subset vT⟩
lemma funds_castSt (U:Set (Points 2)) (w:IsOpen U)(b:_root_.Nonempty U) : ∃ (p:skit) (r:ℝ), 0<r∧openCoastSt U p r∧ ∃ F G:Curtain, Rampart.Supported F G p (r/2):=by
 obtain ⟨⟨x,e⟩⟩:=b; let y:= frontage (WithLp.ofLp (x 0)) (WithLp.ofLp (x 1)); have he:cameo y=x:=by ext1 i; fin_cases i<;>rfl
 have ht: Continuous (fun p:Vantage×Vantage=> cameo (frontage p.1 p.2)):=by
    let f(x:Vantage× Vantage): Fin 2→ E4:=![WithLp.toLp 2 x.1,WithLp.toLp 2 x.2]
    have hv:Continuous f:= continuous_pi (fun i=> by
       fin_cases i; · exact (PiLp.continuous_toLp ..).comp continuous_fst
       exact (PiLp.continuous_toLp ..).comp continuous_snd)
    exact (PiLp.continuous_toLp ..).comp hv
 have hv: {x: Vantage×Vantage| cameo (frontage x.1 x.2) ∈ U} ∈ 𝓝 (y false,y true):=(w.preimage ht).mem_nhds (show cameo y∈ U from he.symm ▸ e)
 obtain ⟨v',s',s⟩:= Metric.mem_nhds_iff.mp hv; let a:= v'/2; have h0:0<a:=half_pos s'; have hA: openCoastSt U y a:= fun i p j u=> s (show (i,j)∈ ball (y false,y true) v' from (ball_prod_same (y false) (y true) v') ▸ (show (i,j)∈ ball (y false) v' ×ˢ ball (y true) v' from ⟨Metric.closedBall_subset_ball (half_lt_self s') p,Metric.closedBall_subset_ball (half_lt_self s') u⟩))
 exact ⟨y,a,h0,hA,anyCastSt y a h0⟩
lemma generalSight_st (A B:Points 1→ℂ) (f:∀ p:Points 1,flightTimes p∈ east 1→ A p=B p):(∫ p:Vantage, A (Polaris.dot p) ∂ F.ppm) = ∫ p:Vantage, B (Polaris.dot p) ∂ F.ppm := integral_congr_ae (Eventually.of_forall fun q=> f _ (dawn_one_st _))
lemma dawningSight_st (h:0<T) (r:ℝ) (hr:0<r)
 (q:Rampart.Supported F G p (r/2)) (x : ∀ l∈closedBall (p false) r,∀ v∈closedBall (p true) r,2*T< v 3-l 3)
 (A B:Points 2→ℂ)(f:∀ p:Points 2,flightTimes p∈ east 2→ A p=B p): (∫ q: Vantage× Vantage, A (Polaris.cameo (frontage q.1 q.2))∂(F.ppm.prod G.ppm))=∫ q: Vantage× Vantage, B (Polaris.cameo (frontage q.1 q.2))∂(F.ppm.prod G.ppm):= integral_congr_ae ((Curtain.covered F G).mono fun z u=>f _ (dawn_pair_st _ T h (x _ (closedBall_subset_closedBall (half_le_self hr.le) (q.basis₀ u.1)) _ (closedBall_subset_closedBall (half_le_self hr.le) (q.basis₁ u.2)))))
#print axioms funds_castSt
#print axioms dawningSight_st
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
end
