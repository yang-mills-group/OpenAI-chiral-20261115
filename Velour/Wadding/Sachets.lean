import Velour.Wadding.Wadding
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

open scoped ContDiff

abbrev foldSpace : E4 ≃L[ℝ] Vantage:= EuclideanSpace.equiv Axis ℝ

lemma foldSpace_preserves: MeasurePreserving foldSpace:= EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _

lemma sachet_compact (F:SampleDose):HasCompactSupport (fun y:E4=>(F.val (foldSpace y):ℂ)):=
 (F.budget.comp_homeomorph foldSpace.toHomeomorph).comp_left Complex.ofReal_zero

/-- Use exactly the independently tuned real weights also on the real edge. -/
def sachet_LocalFieldBounds (F:SampleDose):Test4:=
 (sachet_compact F).toSchwartzMap (Complex.ofRealCLM.contDiff.comp (F.smooth.comp foldSpace.contDiff))

lemma sachet_local(F:SampleDose):LocalTest (sachet_LocalFieldBounds F):= sachet_compact F

lemma sachet_bar(F:SampleDose):bar (sachet_LocalFieldBounds F)=sachet_LocalFieldBounds F:=by
 ext1 y
 exact Complex.conj_ofReal _

lemma sachet_support(F:SampleDose):
 tsupport (sachet_LocalFieldBounds F)= (foldSpace) ⁻¹' tsupport F.val:=by
 unfold tsupport
 rw [show Function.support (sachet_LocalFieldBounds F)=(foldSpace) ⁻¹' Function.support F.val from ?_]
 · exact (foldSpace.toHomeomorph.preimage_closure _).symm
 ext y; exact not_congr Complex.ofReal_eq_zero


lemma integral_sachet {H:Type}[NormedAddCommGroup H][NormedSpace ℝ H](f:E4→H):
 (∫ y:E4, f y)=∫ q:Vantage, f (foldSpace.symm q):=
 (((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    Axis).symm).integral_comp' f).symm

lemma sachet_one(F:SampleDose)(h:F.Normalized): (∫y:E4, sachet_LocalFieldBounds F y)=1:=by
 rw [integral_sachet]
 change (∫ q:Vantage,(F.val q:ℂ))=1
 rw [integral_complex_ofReal,h.2,Complex.ofReal_one]

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "D"=> (Σ₁).muslin

def Bobbin.serves (b:P.Bobbin j x)(F:SampleDose): Module.End ℂ D:=
 P.detects j x b (sachet_LocalFieldBounds F)

lemma Bobbin.pocketed (b:P.Bobbin j x)(F:SampleDose) {O:Set Vantage}
   (p:tsupport F.val ⊆ O) :
 b.serves P j x F ∈ pocket (P.detects j x) (foldSpace ⁻¹' O):=by
  -- placement
  have e:sachet_LocalFieldBounds F∈OS.Semigroup.placement (foldSpace ⁻¹' O):= by
     change tsupport _ ⊆ _
     rw [sachet_support]
     exact preimage_mono p
  exact grove_seed b e

lemma Bobbin.real_Kiss(b:P.Bobbin j x)(F:SampleDose):
 (Σ₁).Faces (b.serves P j x F) (b.windBack.serves P j x F):=by
   simpa [serves,sachet_bar F] using b.op_star (sachet_LocalFieldBounds F)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

