import YM.SU5.SatinWard.Resolution.Nectar
import GaugeFieldConstruction.StencilRope
import YM.SU5.Registration.Rasp.PitchJet
import YM.SU5.Same.PrismReality

/-!
# Divergence of the billed point current inside the W-order domain

Proven from the levy equation at strict wall; `valise` uses Tw= duration symbol. Smeared
reconstruction on rapid domain over actual Ash & actual preparation. Sign & orientation fixed
as in the two ontact conventions (+Eu mass but actual star Weyl); not Eu-only perturbative.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 330000
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
open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers
open CF.Papyrus.Franc.Loaves
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open Fame.Regulator Fame.Regulator.Internal
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble Fame.PSE MarbleFace
open MezzoBill
namespace Discipline
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ν"=> P.advocate 3 x 3
local notation "B!"=> P.ManyF 3 ν
local notation "T_Δ"=> P.seasons 3 ν
open _root_.YM.SatinRegistration _root_.YM.SatinWFixed Carton
open _root_.YM.SatinJets _root_.YM.SatinJets.Drums
open _root_.YM.Boundary _root_.YM.CF.Buffered.Afterglow.Hierarchy Seld MeshClock.Carousel Six
-- precision coordinates time-last, species first. banner orientation in §. Mirror needed for reading star but not this price.L
local notation "DK_" => radial T_Δ
variable {G:Type*}[AddCommGroup G][Module ℂ G] (V: Carton (P.seasons 3 (P.advocate 3 x 3)) G)
variable (J:Axis → ℝ→ℝ→ (P.ManyF 3 (P.advocate 3 x 3)).Op)(qα:Axis→G)(p:∀ i l,0<l→V.bar l (qα i)=J i l l)(y: ∀ i, (P.seasons 3 (P.advocate 3 x 3)).Credits 0 (J i))
variable (O:G)(Λ:ℂ)(hq:Λ≠0)
-- divergence sign witness. no adjust normalization by tuning x.
local instance (priority:= high) priceStOP (P:Spine)(x:P.Spectrum0 3):NormedSpace ℝ (P.ManyF 3 (P.advocate 3 x 3)).Op := opRn (P.ManyF 3 (P.advocate 3 x 3)) -- check opRn type
variable (hX:∀ (l:ℝ≥0),0<l→ (∑ j:Axis, Fame.Regulator.Internal.levy P 3 (P.advocate 3 x 3) (J j) l l j)= Λ • V.bar l O)
  (W: ∀ (l:ℝ≥0),0<l→∀ j:Axis,j≠3→ DifferentiableAt ℝ (fun z:Vantage=> P.locate 3 (P.advocate 3 x 3) z (J j l l)) 0)
include p y W
include hX hq
lemma erase_heat (f:Test4): V.operator O f = Λ⁻¹ • ∑ i:Axis,V.operator (qα i) (takeDerivative i f) :=erase_heat_st P x V J qα p y O Λ hq hX W f
#print axioms erase_heat
end Discipline
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
end
