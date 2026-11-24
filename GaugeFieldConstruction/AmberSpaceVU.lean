import GaugeFieldConstruction.JapaSaleVU
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
-- historically authorized from Native catalogue once for every array. Gauge-invariant. Local supports paid uniformly.
variable {t:ℕ} {Y:Set Vantage}
noncomputable def treasuryVU(t:ℕ)(Y:Set Vantage): Subalgebra ℂ P.Test where
 carrier:={x|P.asked_at t x Y ∧ x∈enclave P.calibration}
 mul_mem' :=fun {a b} ha hb=>by
    obtain ⟨⟨A,u,h⟩,w⟩:=ha;obtain ⟨⟨T,v,e⟩,d⟩:=hb
    exact ⟨⟨A∪T,(bay P.calibration (A∪T) true).mul_mem (tallerBay _ _ _ Finset.subset_union_left u) (tallerBay _ _ _ Finset.subset_union_right v), (P.pin_union ..).symm ▸ Set.union_subset h e⟩,(enclave _).mul_mem w d⟩ -- tune
 add_mem' :=fun {a b} ha hb=>by
    obtain ⟨⟨A,u,h⟩,w⟩:=ha;obtain ⟨⟨T,v,e⟩,d⟩:=hb
    exact ⟨⟨A∪T,(bay P.calibration (A∪T) true).add_mem (tallerBay _ _ _ Finset.subset_union_left u) (tallerBay _ _ _ Finset.subset_union_right v), (P.pin_union ..).symm ▸ Set.union_subset h e⟩,(enclave _).add_mem w d⟩
 algebraMap_mem' c:=⟨⟨∅, (bay _ _ _).algebraMap_mem c,by simp [pinFoot]⟩,(enclave _).algebraMap_mem _⟩ -- tune
lemma AskmonoVU {Z:Set Vantage}(h:Y ⊆ Z): treasuryVU (P:=P) t Y ≤ treasuryVU t Z:= by rintro i ⟨⟨V,H,W⟩,q⟩; exact ⟨⟨V,H,W.trans h⟩,q⟩
variable {X:P.Test}
lemma chestVU (x:Cover){y:ℝ}(h:CutterVU x t X)(b:PlethoraJ P t<y): X ∈ treasuryVU t (ball (P.meshPose t x) y):=⟨⟨cartO (SceneAtN P x) 28,h.2, fun z t'=> (FixtureN P t x _ t').trans_lt b⟩, h.1⟩ -- tune Pelthora
variable {I:Type}[Fintype I][DecidableEq I] (L:List I)(xF:I→ℕ→P.Test)(C:I→ScreensJ P)(e:∀ i,PerformerVU (xF i) (C i))
include e
lemma certifyVU (W:I→Set Vantage)(K:Set (SpaceN I))(X:SpaceN I→ℂ)(h:IsCompact K)(v:∀ i, IsOpen (W i))(g:∀ i x,x∈K→ VantageN x i∈ W i) : ∀ᶠ t in atTop, (∀ i∈DustyN P K t h,∀ j:I,P.chartAll (TownN i j) (xF j t)∈ treasuryVU t (W j)) ∧ NativeCostN xF L K h X t∈ treasuryVU t (⋃ i,W i) :=by
 let S(i:I):=(fun x=> VantageN (I:=I) x i) '' K
 have hv (i:I): IsCompact (S i):= h.image ((continuous_apply i).comp FormalV_N)
 have hG(i:I): S i⊆ W i:= Set.image_subset_iff.mpr (fun x h=>g i x h)
 choose L' Z F' using fun i=> (hv i).exists_thickening_subset_open (v i) (hG i)
 filter_upwards [eventually_all.mpr (fun i:I=> (e i).2),eventually_all.mpr (fun i:I=>(SecondEraJ P).eventually (gt_mem_nhds (Z i)))] with s p t
 have ht(i:MeshN I)(l:i∈DustyN P K s h)(j:I):P.chartAll (TownN i j) (xF j s)∈ treasuryVU s (W j):=by
    apply AskmonoVU (Set.Subset.trans ?_ (F' j)) (chestVU (TownN i j) (p j _) (t j))
    rw [thickening_eq_biUnion_ball]
    have he:P.meshPose s (TownN i j)∈ S j:=⟨_,(dustN _ _ _ _ i).mp l,rfl⟩ -- tune
    intro x v; exact Set.mem_iUnion₂.mpr ⟨_,he,v⟩
 let Z':= treasuryVU (P:=P) s (⋃ i,W i)
 refine ⟨ht,Z'.sum_mem fun i h'=>Z'.smul_mem ?_ _⟩; unfold MoneyPoseN; apply Z'.list_prod_mem; intro a he; obtain ⟨x,-,rfl⟩:=List.mem_map.mp he; exact AskmonoVU (Set.subset_iUnion _ x) (ht i h' x) -- tune
omit e in
lemma apportVU (G:Set Vantage)(x:P.Test)(t:ℕ)(h:x∈treasuryVU t G): x∈enclave P.calibration ∧ P.asked_at t x G:= And.symm h -- tune
#print axioms certifyVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end



