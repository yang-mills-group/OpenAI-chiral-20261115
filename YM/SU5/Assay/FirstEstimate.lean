import SatinFixedContrastNovember4
import YM.SU5.Assay.Dawn
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Prototype Ballad Cordial Set Six
variable {P:Spine}{R:P.Register}{x:P.Spectrum0 3}{c r:ℕ→ℕ}
variable {D N:Doorway}{o:Orders}
/-!
## First, partial result on the actual coupling

This is a **contact** and efficacy estimate so far. New nonzero margin
for the split test with genuine narrowing; no excitation purchase yet.
With `Company`, also acquires the quantitative `Lock` endowment of the
charged display against any simultaneously financed owner, not just
the unit calibrator here. Commitment in every case is to `Dawn`'s one
vote; the voted course is bought even before the rectangles. Not
claiming to modify some earlier not-similarly-paid course after election.
-/
namespace Strategy
variable (p:P.Strategy R c r x)
include p
lemma first_estimate (y:D.Later N o 0) :
 ∀ᶠ i in atTop,P.Taps x (c i) (r i) D N o ∧ ∃M:P.Menagerie,P.Company (r i) M (1/2) ∧
    (∀F G,P.Fresco R x (c i) (r i) D N o F G → P.Dawn R x (c i) (r i) D N o F G M) ∧
     ∃F G,P.Dawn R x (c i) (r i) D N o F G M:=by
 filter_upwards [p.reaches y,p.offer (show 0<1/(2:ℝ) by norm_num)] with i t z
 obtain ⟨M,h⟩:=z
 obtain ⟨F,G,q⟩:=p.exposes t
 exact ⟨t,M,h,fun _ _ v=>v.dawn p.reserves h,F,G,q.dawn p.reserves h⟩
lemma morning:
 ∃ (i:ℕ) (M:P.Menagerie) (F G:SampleDose),P.Dawn R x (c i) (r i) reviewEarlierBox reviewLaterBox fullWay F G M:=by
 obtain ⟨i,_,M,_,_,F,G,r⟩:=(p.first_estimate fullSweep).exists;exact ⟨i,M,F,G,r⟩
end Strategy

/-- Unconditional, explicit registration and both boxes; each qualification and
 each norm bound is on **one and the same** course and voted law. More precisely
 `survey_purchase` and `Strategy.first_estimate` pay even with arbitrary initial
 suppliers before the experiments. -/
abbrev simpleRequest : Supplier:= fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem satinEarliest :
 ∃ (P:Spine) (R:P.Register), uniform P R simpleRequest 1 1 ∧
   ∃ (c r:ℕ→ℕ) (x:P.Spectrum0 3), id≤r ∧ P.Strategy R c r x ∧
    ∃(i:ℕ) (M:P.Menagerie) (F G:SampleDose),
      P.Dawn R x (c i) (r i) reviewEarlierBox reviewLaterBox fullWay F G M:=by
 obtain ⟨P,R,h,_,c,r,x,w,q⟩:=survey_purchase ordinaryAdmission simpleRequest 1 1 (by norm_num) id
 exact ⟨P,R,h,c,r,x,w,q,q.morning⟩

#print axioms satinEarliest
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
