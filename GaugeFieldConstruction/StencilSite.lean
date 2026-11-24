import GaugeFieldConstruction.StencilFamily
import YM.SU5.SatinWard.Resolution.FigureJ
import YM.SU5.SatinWard.Resolution.CasterH
import GaugeFieldConstruction.MindFrameNX
import GaugeFieldConstruction.PhysicalBook
import YM.CF.Continuum.Cadenza

/-!
# Current identification on the meters. Lead 0 (no links, no nonzero separation, current
 really over the first-spin frames). Can *normalize* on the same branches, no appearance of
 the Stock vacuum coefficient. Not a collar estimator.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers
open CF.Papyrus.Franc.Loaves
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open Fame.Regulator
open BProof Pressure CF.Tap
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Ione.Clock Moto
open Preparation.Yoke
open ShapeLab ResolutionFrame
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField

namespace Discipline
open Lead
open Lamour.Bridge.Celeste
open YM.GaugeFieldConstruction.Matter
variable (P:Spine) (p:Cover) (a:Axis)(v:Soul)
private lemma chiralPays (z:Soul) : neutral (dynamicSpin z):=fun g=> ((show ChiralX 0 (dynamicSpin z) from (Θc.equivFun.symm z).property).color g).symm.eq
private noncomputable def colorRow (v:Soul): VFlavorNX → ℂ:= ((species (dynamicSpin v)).1 (chiralPays v)).choose
private lemma colorsBills (z:Soul): jordan (colorRow z)=dynamicSpin z:= ((species (dynamicSpin z)).1 (chiralPays z)|>.choose_spec).1.symm
noncomputable def FlavorCost : Soul →ₗ[ℝ] (VFlavorNX→ℂ) where
 toFun := colorRow
 map_add' a b:=by apply co_earn; change jordan _ = jordan _; rw [jordan.map_add,colorsBills,colorsBills,colorsBills]; exact congrArg Subtype.val (Θc.equivFun.symm.map_add a b)
 map_smul' r v:=by apply co_earn; change jordan _ = jordan (r • _); rw [← Complex.coe_smul,jordan.map_smul,colorsBills,colorsBills,Complex.coe_smul]; exact congrArg Subtype.val (Θc.equivFun.symm.map_smul r v)
local notation "Index"=> VFlavorNX × Fin 2 × Fin 2
abbrev revReading (p: Cover): Lead 0 := Ballad.noLagSt p
abbrev siteStake (p:Cover)(i: VFlavorNX × Fin 2 × Fin 2) := P.plaqueStakeNX (revReading p,i)
noncomputable abbrev bath (a:Axis)(i: VFlavorNX × Fin 2 × Fin 2):Soul →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap ((petal a (upSpin i.2.1) (dnSpin i.2.2)) • (LinearMap.proj i.1 ∘ₗ FlavorCost))
lemma stakesRepresent : planC P p a (dynamicSpin v)=∑ i: VFlavorNX × Fin 2 × Fin 2,bath a i v • siteStake P p i:=by
 apply Subtype.ext;
 have h:= truePocket_st P.calibration (p:=colorRow v) (colorsBills v).symm (gardenForm P.calibration a (dynamicSpin v) p);
 change gardenFlower P.calibration p a (dynamicSpin v)= _; change _= (screenHall P.calibration).val (∑ i:Index,bath a i v • siteStake P p i); rw [h,map_sum]; apply Finset.sum_congr rfl; intro j _; rfl
#print axioms stakesRepresent
end Discipline
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
end
