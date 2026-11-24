import GaugeFieldConstruction.AmberOasisVU
import GaugeFieldConstruction.LayoutKinVU
import GaugeFieldConstruction.CameraTxnVU
import GaugeFieldConstruction.UpheldMercuryVU
import GaugeFieldConstruction.RevelatoryVU
import GaugeFieldConstruction.QuaffShoreVU
import GaugeFieldConstruction.PalaceScopeVU
import GaugeFieldConstruction.SavorVU
import GaugeFieldConstruction.GlacierVU
import GaugeFieldConstruction.BenedictVU
import GaugeFieldConstruction.VisPriceVU
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
-- actual Coalition: one spine/view/archive, one registration, one path, and APPROVED solicitation of orientation frame and dynamics. Predicate open Badge to allow further needs while preserving same purchases.
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration -- tune

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
-- main underwriting record.VU. all data generated. abstract REALIZED with a.e qualifications, specifying one spectrum. unproblematic along P path
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace
variable {P:Spine} {R:P.Register}{c:P.Poll 3}{x:P.Spectrum0 3}{A:Set Vantage}{s i k:ℕ}
open Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open Reconstruction
open Set
-- broaden menus (P.asked_at). reuse Poll from convert with exact costs. Share same labels. S_attrs with Orbit.Binding.
-- Sharp via ACT.Unselected (same depth schedule!) Using MeterQueryVU any supports, mosaic orientation ok.
lemma cratePV {l:List (MeterQueryVU P)} (h:∀ i∈l,i.1∈ treasuryVU s i.2)(p:l.Pairwise (fun a b=>Disjoint a.2 b.2)) :
   ∃ K:MeterQueryVU P →Set Vantage, (∀ i∈l,K i⊆ i.2 ∧ IsCompact (K i) ∧ P.asked_at s i.1 (K i)) ∧
     let W:= TopCurrencyVU P s (l.map (fun x=>(x.1,K x)))
     (∀ᶠ i in atTop,TenderΘVU s (P.diagonalᵢ i) (P.diagonalₖ i) W) ∧ Tendsto (fun i=> AskingPriceVU P i W) atTop (𝓝 (P.E s (((l.map Prod.fst).prod).val))) :=by
 choose! K t using fun i (v:i∈l)=> MayCollectVU (show P.asked_at s _ _ from (h i v).1)
 refine ⟨K,t,?_⟩; intro W
 let L : List (MeterQueryVU P):= l.map (fun x=>(x.1,K x)); let f:= (l.map Prod.fst).prod
 have hV: L.Pairwise (fun a b=> Disjoint a.2 b.2):= List.pairwise_map.mpr <| p.imp_of_mem fun a b h'=> h'.mono (t _ a).1 (t _ b).1
 have he: ∀ᶠ i in atTop,TenderΘVU s (P.diagonalᵢ i) (P.diagonalₖ i) W:= by
    refine productionTopVU (s:=s) (l:=TopCurrencyVU P s L) ?_ ?_ (List.pairwise_map.mpr hV)
    · rintro j q; change j∈ TopCurrencyVU P s L at q; obtain ⟨I,v,rfl⟩:=List.mem_map.mp q; obtain ⟨i,x,rfl⟩:= List.mem_map.mp v; exact pin_legalVU (V:=(i.1,K i)) (h i x).2 (t i x).2.2
    rintro j q; change j∈ TopCurrencyVU P s L at q; obtain ⟨I,v,rfl⟩:=List.mem_map.mp q; obtain ⟨i,x,rfl⟩:= List.mem_map.mp v; exact (t i x).2.1
 have hx : ΞProdVU W=P.slotHole s f:=by
    have q (y:List (MeterQueryVU P)): ΞProdVU (TopCurrencyVU P s y)=P.slotHole s ((y.map Prod.fst).prod):=by
      induction y with
      | nil=> exact (map_one (pinhole P.Test s)).symm
      | cons a l ih=> simp only [TopCurrencyVU,List.map_cons,List.prod_cons,prod_consVU]; rw [show _=P.slotHole s ((l.map Prod.fst).prod) from ih]; exact (map_mul (pinhole P.Test s) _ _).symm
    change ΞProdVU (TopCurrencyVU P s L) =_; rw [q L]; exact congrArg _ (congrArg List.prod (show L.map Prod.fst=l.map Prod.fst from List.map_map ..))
 refine ⟨he,(P.IntoPaperVU f s).congr' (he.mono fun i v=>?_)⟩
 rw [← recordedAt (u:=f) _ P.large _ _ _ v.pay, ← show ΞProdVU W=pinhole _ s f from hx]
 exact v.value.2.2.2 -- proof tune
#print axioms cratePV
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
