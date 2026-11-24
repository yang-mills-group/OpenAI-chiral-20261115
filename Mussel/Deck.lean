import Mussel.Spread
import YM.SU5.Relativistic.TrueSeparation
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
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Broker
variable (P:Spine)(W:Bool)(s t:ℕ)(i:Cover)
local notation "K₀"=>P.calibration
open Tower.Reconstruction
abbrev pilot(x:P.Test):P.Test:=P.chartAll i (P.conveying s (t-s) x)
abbrev fence(A:Finset Cover):Finset Cover:=P.placeSet (volumeAround P.par P.width (t-s) A) Vacancy.ordinate i
variable {P}{A D:Finset Cover}{x y:P.Test}
lemma tram (p:x∈bay K₀ A true):pilot P s t i x∈bay K₀ (fence P s t i A) true := P.place_test _ Vacancy.ordinate i (by
 exact (Tower.proceeds P.run P.large P.history.circuit s (t-s) ((Tapestry.locates ..).1 p)).1)
lemma stretch(h:s ≤ t){q:Vantage}(p:q∈P.pinFoot t (fence P s t i A)): q-P.meshPose t i∈P.pinFoot s A:=by
 have ht:= P.place_back_pin t _ Vacancy.ordinate i p; rw [P.jettyT_full] at ht
 exact P.pin_onward s t A h ht
lemma trailer (p:x∈bay K₀ A true)(q:y∈bay K₀ D true)(d:Disjoint (P.pinFoot s A) (P.pinFoot s D)):
 pilot P s t i (x*y) = pilot P s t i x*pilot P s t i y:=by
 let B':=P.conveying s (t-s)
 have he:B' (x*y)=B' x * B' y:=by
    apply Subtype.ext; change stream P.run P.large P.projection.refine s (t-s) (x.val*y.val)=stream _ _ _ s (t-s) x.val*stream _ _ _ s (t-s) y.val
    rw [P.usual_footprint,P.usual_footprint] at d
    exact woven_product P.run P.large P.history.circuit s _ ((Tapestry.locates ..).mp p) ((Tapestry.locates ..).mp q) (separated_in_foot P.par P.width s A D d)
 exact (congrArg (P.chartAll i) he).trans (map_mul (P.chartAll i) (B' x) (B' y))
variable (L:List Axis)
/- instead of creating big Aprons repeat onward proof. expose /
At birth H sensing D. as spec.Board. -/
lemma commute {F:P.Test} (p:F∈ P.sensing A s W)(u:s ≤ t): pilot P s t i F ∈ P.sensing (fence P s t i A) t W :=by
 let n:=t-s; let D':=Vacancy.ordinate
 let z:=pilot P s t i; let X':=P.sensing (fence P s t i A) t W
 refine Submodule.span_induction (s:=_) (p:=fun f _=> z f ∈ X') (fun f v=>?_) ?_ ?_ ?_ (show F∈ P.sensing A s W from p)
 · obtain ⟨S₁,T₁,V',h,hh,w,e,v⟩:=v
   let g:=(volumeAround P.par P.width n)
   have hs:S₁ ⊆ V':= Finset.subset_union_left.trans h
   have ht:T₁ ⊆ V':= Finset.subset_union_right.trans h
   have who:= P.cruise_keeps_charge W D' i _ _ _ (x:=P.conveying s n f) (P.onward W S₁ T₁ V' s _ hs ht e n)
   refine Submodule.subset_span (show _∈_ from ⟨_,_,_,?_,?_,?_,who,P.cruise_color D' i (P.refine_keeps s _ v n)⟩)
   · exact union_subset (P.place_mono (g S₁) (g V') D' i (P.vol_mono n hs)) (P.place_mono (g T₁) _ D' i (P.vol_mono n ht))
   · exact P.place_mono (g V') _ D' i (P.vol_mono n hh)
   exact P.place_distinct t _ _ D' i (w.mono (P.pin_onward s t _ u) (P.pin_onward s t _ u))
 · unfold z pilot; rw [P.vanishes_receipt,map_zero]; exact X'.zero_mem
 · intro a b _ _ h l; rw [show z (a+b)= z a + z b from (congrArg (P.chartAll i) (P.later_receipt ..)).trans (map_add ..)] -- map_add .. inference
   exact X'.add_mem h l
 intro a b _ h; rw [show z (a • b)=a • z b from (congrArg (P.chartAll i) (P.scaled_receipt ..)).trans (map_smul ..)]
 exact X'.smul_mem _ h

end Broker
#print axioms Broker.commute
#print axioms Broker.trailer
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
