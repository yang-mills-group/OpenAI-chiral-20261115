import YM.SU5.Assay.WardNotes
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s:ℕ}{W:Bool}
local notation "K"=> P.calibration
/-!
# Integrated comparator price (earlier or later, independent test weights).

Preserve even the same basis choice through arbitrary refinements in the pre-
posing prescription; as well as the canonical post-resolution comparison,
with termwise post-assignment available up to and including the actual smear
paid as a whole. Bodies can already have a reflected orientation when entering
here. Read post consultation as in SatinFixedContrastNovember4, even just
factoring with either single Ward jurisdiction suffices there. See WardNotes.
-/
variable (P)(x:P.Spectrum0 3)(t:ℕ)(A B:P.Apron)(F G:SampleDose)(l n:List P.JointPiece)

def PriorTithe:ℂ:=∑r∈P.usedGrid t F,P.activation t F r*P.PriorSingle x t A l r
def PriorBoth:ℂ:=∑r∈P.usedGrid t F, ∑o∈P.usedGrid t G,
  P.activation t F r * P.activation t G o * P.PriorPair x t A B l n r o

variable {P}
local notation "Q"=> P.paperSplit t x
lemma PriorTithe.zero (p:Presented K W A.S A.F l) (v:A.s≤t)(R:P.Register):P.PriorTithe x t A F l=0:=Finset.sum_eq_zero fun r _=> mul_eq_zero_of_right _ (sParcel.offer x t A p v r R).zero
lemma PriorBoth.zero {V:Bool}(p:Presented K W A.S A.F l)(q:Presented K V B.S B.F n)
 (v:A.s≤t)(w:B.s≤t)(d:Disjoint (P.spacePrice A F) (P.spacePrice B G))(R:P.Register):P.PriorBoth x t A B F G l n=0:=by
 refine Finset.sum_eq_zero fun r j=> Finset.sum_eq_zero fun o k=>mul_eq_zero_of_right _ ?_
 have m:(P.Aperture A (P.meshPose t r)) ⊆ P.spacePrice A F:= Set.subset_iUnion₂_of_subset (P.meshPose t r) ((P.usedPose _ _ _).mp j) Set.Subset.rfl
 exact Offer.versus (sParcel.offer x t A p v r R) (sParcel.offer x t B q w o R) (d.mono m (Set.subset_iUnion₂_of_subset (P.meshPose t o) ((P.usedPose _ _ _).mp k) Set.Subset.rfl))

/-- `DressCall`: shows real neutral certificate with beam  (at the level
of raw OS bills -- here neutral means precisely `enclave`),
including reflected versions as soon as they are taken as probe. And finances
for every tested pose and independent smear. -/
structure DressCall (P:Spine)(x:P.Spectrum0 3)(A:P.Apron)(W:Bool)(l:List P.JointPiece) : Prop where
  mixed: A.Beams W
  presented:Presented P.calibration W A.S A.F l
  native:P.PostAsk A.s x A.F (P.Aperture A 0) W
  /-- Each finer actual smear, priced canonically and with prior assignments. -/
  finer:∀ t≥A.s,∀ F:SampleDose,
    P.PostAsk t x (P.prepared t A F) (P.spacePrice A F) W∧
    P.PriorTithe x t A F l=0 ∧
    ∀ r,P.PostAsk t x (P.issuing t A r) (P.Aperture A (P.meshPose t r)) W∧P.Offer x t A l r

theorem dressSpecific (h:A.Beams W)(v: Presented K W A.S A.F l)(R:P.Register):P.DressCall x A W l:=
 ⟨h,v,h.native x,fun _ e F=>⟨h.projection x e F,PriorTithe.zero x _ A F l v e R,fun r=>⟨h.backdrop x e r,sParcel.offer x _ _ v e r R⟩⟩⟩
theorem dress_any (h:A.Beams W)(R:P.Register): ∃ l,P.DressCall x A W l:= by
 obtain ⟨l,v⟩:=Beam.present h; exact ⟨l,dressSpecific _ _ _ h v R⟩
variable {t A B l n x}
/-- Thus joint reading predicted zero both ways, at every eligible sold grid,
regularity of the smear not otherwise constrained. -/
theorem DressCall.joint {V:Bool} (v:A.s≤t)(w:B.s≤t)(d:Disjoint (P.spacePrice A F) (P.spacePrice B G))(p:P.DressCall x A W l)(q:P.DressCall x B V n)(R:P.Register) :
 P.PostAsk t x (P.prepared t A F*P.prepared t B G) (P.spacePrice A F ∪ P.spacePrice B G) W ∧
 P.paperSplit t x (P.prepared t A F*P.prepared t B G)=0 ∧ P.PriorBoth x t A B F G l n=0:=by
 have a:=p.mixed.survey x v F w G d
 exact ⟨a,a.zero x, PriorBoth.zero x _ _ _ F G l n p.presented q.presented v w d R⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
