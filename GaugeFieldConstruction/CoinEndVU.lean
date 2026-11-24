import GaugeFieldConstruction.VoyMouthVU
import GaugeFieldConstruction.VoxPaperVU
import GaugeFieldConstruction.TallSeasVU
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
variable (G:Fin n→SampleDose)
noncomputable abbrev SponVU : Set (Points n):= {x| ∀ i, (x i).ofLp∈tsupport (G i).val}
lemma cardCoinVU : tsupport ⇑(ConjoinVU n G) ⊆ SponVU n G:=fun x v i=> extentCoinVU G _ v i
lemma VicTerraVU (v:SponVU n G⊆ TerraVU n) : HabVU G ⊆ VantageN ⁻¹' MasksR (Fin n):=by
 intro x h; let y:=(ExpositionVU n).symm x; have he:ExpositionVU n y=x:= (ExpositionVU n).apply_symm_apply _; rw[←he] at h ⊢; have hp:= v (show y∈ SponVU n G from fun i=> h i (Set.mem_univ _)); change VantageN ((ExpositionVU n) y)∈MasksR (Fin n); exact ((ephemVU n y).symm ▸ (show ΦplanR n y∈ _ from hp)) -- rw at * bad
noncomputable abbrev MenuFieldVU (x:Points n):=ConjoinVU n G x
noncomputable abbrev EraScoreVU (t:ℕ):=∏ i, installedN (vF i) (G i) t
lemma funcHeightVU : ΞHeightsVU G ∘ (ExpositionVU n)=⇑(ConjoinVU n G):=by
 funext x; rw [Function.comp_apply]; unfold ConjoinVU; rw [YM.Boundary.Joint.material_at]; change ((∏ i, (G i).val (x i).ofLp:ℝ):ℂ)=∏ i, ((G i).val (x i).ofLp:ℂ); push_cast <;> rfl -- tune
include J
lemma HearthPackVU (v:SponVU n G ⊆ TerraVU n) : Tendsto (fun t=> Cε.cash t (EraScoreVU n vF G t)) atTop (𝓝 (EuMenuVU n Cε F (ConjoinVU n G))) :=by
 have he := ValuePackVU Cε vF F (List.finRange n) (deckΦP n) J G (VicTerraVU n G v)
 suffices EuMenuVU n Cε F (ConjoinVU n G)=∫ x, SpokenN Cε F (ΞHeightsVU G) x by rw [this]; exact he
 rw [← (expositionMeasureVU n).integral_comp (ExpositionVU n).toHomeomorph.measurableEmbedding]; refine integral_congr_ae (Eventually.of_forall fun i=>?_); change ConjoinVU n G i *_= _; have h:=congrFun (funcHeightVU n G) i; rw [←h]; change _=_* SπR _ _ (VantageN ((ExpositionVU n) i)); rw [ephemVU]; rfl
#print axioms HearthPackVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end


