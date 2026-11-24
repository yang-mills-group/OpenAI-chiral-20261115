import SatinFixedContrastNovember4
import YM.SU5.Six.ViewHom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable (P:Spine)(Z:Lead.Clan)(s n:ℕ)
local notation "A"=> P.experimentBody Z s n
/-- The undifferenced mixed link/CAR charged component, with its absolute 1-pt
normalizer. At physical seats it collapses to 1 (though note raw factorized).
Support/clock kept the same as in the existing reciprocity measurements. -/
lemma abode : P.defaultR Z n ∈ bay P.calibration (P.measureStencil n) true:=
 Subalgebra.smul_mem _ (tallerBay _ _ _ subset_union_left (P.visibility ..)) _
lemma real : P.defaultR Z n ∈ enclave P.calibration :=
 Subalgebra.smul_mem _ (P.front_real Z n) _
noncomputable def puppet : P.Apron where
 s:=s
 u:=P.probeClock n
 pos:=P.clock_positive n
 F:=P.defaultR Z n
 S:=P.measureStencil n
 realM:= Habitat.real P Z n
 bay:= abode ..
 shelter:=P.shelters n
local notation "D"=> puppet P Z s n
/-- Pockets well separated (RP reserve). -/
lemma aware (hn:P.calibration.ℓ<n): P.Sensor (puppet P Z s n) Z.2:=by
 let F:=P.flash n; let R:= P.sensing (P.measureStencil n) s Z.2
 have d:= Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchBorn F)
 have e:= Finset.singleton_subset_iff.mpr (Lamour.Bridge.Celeste.porchGone F)
 apply Submodule.smul_mem R
 exact Submodule.subset_span (show _∈_ from ⟨_,_,_,union_subset d e, Finset.subset_union_left,P.pocket_gap s n hn,P.front_charge Z n,P.front_real Z n⟩)
lemma brightR : P.defaultR Z n∈ P.births 3 s:=
 (P.births 3 s).smul_mem _ (P.brightC Z s n)
lemma shine (x:P.Spectrum0 3): let ξ:=P.otherSpectrum 3 3 x; P.viewF 3 ξ s (brightR P Z s n)= (purePrice Z:ℂ)⁻¹ • P.shard x Z s n:=P.view_smul ..
lemma apertureE (o:Vantage): P.Aperture D o=P.Aperture A o:=rfl
lemma pricesE (f:SampleDose):P.spacePrice D f=P.spacePrice A f:=rfl
lemma pricesM (f:SampleDose):P.spacePrice ((D).kiss P 3) f=P.spacePrice ((A).kiss P 3) f:=by unfold spacePrice Aperture; rfl

end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
