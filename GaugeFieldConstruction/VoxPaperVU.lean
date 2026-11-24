import GaugeFieldConstruction.VoyMouthVU
import GaugeFieldConstruction.HoneySilkVU
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
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
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
open SignetS Patrons ChSigFe
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
open YM.Boundary (Test4 Joint)
open MacroGrid
open scoped ContDiff
variable (r s:SampleDose)
variable (n:ℕ)(Cε:CoinsR P)(F:Fin n→ScreensJ P)(vF:Fin n→ℕ→P.Test)(J: ∀ i,VenueX 0 (F i) (vF i))(X:Points n→ℂ)
noncomputable abbrev FlattenLogoVU:= X ∘ (ExpositionVU n).symm
lemma ephemVU (x:Points n): VantageN (ExpositionVU n x) = ΦplanR n x:= by funext i j; rfl -- tune
lemma AreaDiskVU (X:Points n→ℂ) : tsupport (FlattenLogoVU n X)= (ExpositionVU n).symm ⁻¹' tsupport X:=tsupport_comp_eq_preimage _ (ExpositionVU n).symm.toHomeomorph
lemma AuthAreaVU (c:HasCompactSupport X) : IsCompact (tsupport (FlattenLogoVU n X)):=by rw [AreaDiskVU]; exact (ExpositionVU n).symm.toHomeomorph.isCompact_preimage.mpr c
noncomputable abbrev TerraVU:= (ΦplanR n) ⁻¹' MasksR (Fin n)
noncomputable abbrev VoxCostVU (c:HasCompactSupport X)(t:ℕ):=NativeCostN vF (List.finRange n) _ (AuthAreaVU n X c) (FlattenLogoVU n X) t
noncomputable abbrev EuMenuVU (n:ℕ) (c:CoinsR P) (F:Fin n→ScreensJ P)(X:Points n→ℂ):=∫ x:Points n,X x*SπR c.porch F (ΦplanR n x)
include J
lemma CoastNativeVU (h:Continuous X)(c:HasCompactSupport X)(v:tsupport X⊆ TerraVU n) : Tendsto (fun t=> Cε.cash t (VoxCostVU n vF X c t)) atTop (𝓝 (EuMenuVU n Cε F X)):=by
 have ht(y:SpaceN (Fin n))(q:y∈tsupport (FlattenLogoVU n X)): VantageN y∈MasksR (Fin n):=by
    rw [AreaDiskVU] at q; let z:=(ExpositionVU n).symm y; have hp:= v q; exact ((ExpositionVU n).apply_symm_apply y) ▸ ((ephemVU _ z).symm ▸ (show ΦplanR n z∈MasksR _ from hp)) -- tune
 have hw:= DiscoverVU Cε vF F (List.finRange n) (deckΦP n) J _ (AuthAreaVU _ _ c) _ subset_closure (h.comp (ExpositionVU n).symm.continuous) (fun x t=> ht x t)
 have he: EuMenuVU n Cε F X=∫ x, SpokenN Cε F (FlattenLogoVU n X) x:= by
    rw [← (expositionMeasureVU n).integral_comp (ExpositionVU n).toHomeomorph.measurableEmbedding]; refine integral_congr_ae (Eventually.of_forall fun i=>?_); change X i*_= _; dsimp only[SpokenN,FlattenLogoVU,comp_apply]; rw[ephemVU,(ExpositionVU n).symm_apply_apply i]
 rw[he]; exact hw
#print axioms CoastNativeVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end

