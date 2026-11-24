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
lemma MayCollectVU {u:P.Test}(a:P.asked_at s u A) : ∃ K:Set Vantage,K ⊆ A ∧ IsCompact K ∧ P.asked_at s u K:=by obtain ⟨W,l,e⟩:=a; exact ⟨P.pinFoot s W,e,(by rw[P.usual_footprint]; exact footprint_compact ..),W,l,Subset.rfl⟩
-- Menu assignment at EVERY pose. all marginal queries.One height.
local notation "I" => P.diagonalᵢ
local notation "Kq"=> P.diagonalₖ
abbrev PollTrackVU (v:P.Spectrum0 3)(K:P.Register)(c:P.Poll 3):Prop:= P.Selects K 3 v c ∧
 ∀ {J:Type} (L:Finset J) (S:J→ℕ)(l:J→List (MeterQueryVU P)) (ε:ℝ), 0<ε →
   (∀ i∈L, (∀ u∈l i, P.asked_at (S i) u.1 u.2 ∧ u.1∈enclave P.calibration ∧ IsCompact u.2) ∧ (l i).Pairwise (fun a b=>Disjoint a.2 b.2))→
   ∀ᶠ i in atTop,∀ᶠ r:ℕ in atTop,∀ j∈L, SummitInvoiceVU (R:=K) (x:=v) (s:=S j) (c:=c) i r (TopCurrencyVU P (S j) (l j)) ε
namespace PollTrackVU
lemma reachable (v:P.Spectrum0 3)(K:P.Register): ∃ c,PollTrackVU v K c:=P.convertVU K v
variable (Φ:PollTrackVU x R c)
include Φ
lemma asksVU {C:List (MeterQueryVU P)} (e:∀ u∈C,P.asked_at s u.1 u.2 ∧ u.1∈enclave P.calibration)(q:C.Pairwise (fun a b=>Disjoint a.2 b.2)) {ε:ℝ} (w:0<ε) : ∃ K:MeterQueryVU P →Set Vantage,
     (∀ i∈C,K i⊆ i.2 ∧ IsCompact (K i) ∧ P.asked_at s i.1 (K i)) ∧ ∀ᶠ i in atTop,∀ᶠ r:ℕ in atTop, SummitInvoiceVU (R:=R) (x:=x) (s:=s) (c:=c) i r (TopCurrencyVU P s (C.map (fun p=> (p.1,K p)))) ε:=by
 choose! t h using fun i (v:i∈C)=> MayCollectVU (e i v).1
 refine ⟨t,h,?_⟩
 let C' : List (MeterQueryVU P):= C.map (fun i=>(i.1,t i))
 have H: C'.Pairwise (fun a b=>Disjoint a.2 b.2):=List.pairwise_map.mpr <| q.imp_of_mem fun a b h' => h'.mono (h _ a).1 (h _ b).1
 have u (i) (x:i∈C') : P.asked_at s i.1 i.2 ∧ i.1∈enclave P.calibration ∧ IsCompact i.2:=by obtain ⟨i,y,rfl⟩:=List.mem_map.mp x; exact ⟨(h i y).2.2,(e i y).2,(h i y).2.1⟩
 filter_upwards [Φ.2 ({0}:Finset ℕ) (fun _=>s) (fun _=>C') _ w (fun _ _=> ⟨u,H⟩)] with i v; exact v.mono (fun _ k=> k 0 (by simp))
#print axioms asksVU
end PollTrackVU
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
