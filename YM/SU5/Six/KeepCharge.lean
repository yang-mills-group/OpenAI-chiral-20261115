import YM.SU5.Selected.MeshSym
import YM.SU5.Selected.Identify
import YM.SU5.Six.CoverLetters

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Exhibition
namespace Spine
open Six
variable (P:Spine)(W:Bool)(S T D:Finset Cover)(s:ℕ)
local notation "Y"=>P.run
local notation "H"=>P.large
local notation "K"=>P.calibration
local notation "G"=>P.projection
local notation "A₊" X:max=>wingspan P.par P.width X
private lemma charged_ship {N N':Side}(h:N=N')(f:Mark N) :
    (∀ x,f x∈bipocket N W (Satin.region S N) (Satin.region T N)) ↔
      ∀ x,ship h f x∈bipocket N' W (Satin.region S N') (Satin.region T N') := by subst N; rfl
private lemma block_charged {i k:ℕ} (d:S⊆D)(t:T⊆D){F:Buffered.Family P.calibration}(u:F∈ DressedPair K W S T D)
    (h: legalAt Y s i k)(p:Tivoli (A₊ D) ((K).c (momentm Y i (s+1)))):
    block Y H s i k D F∈DressedPair K W (A₊ S) (A₊ T) (A₊ D):=by
  let a:=side Y i (s+1)
  have hp:= dressed_test K W S T D (union_subset d t) u
  let f:=distribute Y H s i F
  apply Six.descend K W (A₊ S) (A₊ T) (A₊ D) _ p (union_subset (wingspan_mono d) (wingspan_mono t)) (booked ..)
  refine (charged_ship W (A₊ S) (A₊ T) (terrain Y H _ (s+1)) _).2 ?_
  change ∀ x, distribute Y H _ i (block Y H s i k D F) x ∈ _
  rw [reserved Y H s D i k h hp p]
  exact ascend_bipocket W Y s i k S T f ((stationed Y H s D i hp).env) ((charged_ship W S T (terrain Y H _ s) _).1 (dressedMatrix K W S T D u _)) h
lemma advance_charged {F:Buffered.Family P.calibration}(p:S⊆D)(q:T⊆D)(u:F∈ DressedPair K W S T D) :
    P.projection.refine s F∈DressedPair K W (A₊ S) (A₊ T) (A₊ D):= by
  let r(i):=P.period ((G).rows i); let m(i):=P.cutoff ((G).columns i)
  have ht : Tendsto r atTop atTop := P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop
  let X:= (A₊ D)
  obtain ⟨n,hp⟩ := (turning Y H (s+1) X).exists
  let J:= momentm Y n (s+1)
  have he:= dressed_test K W S T D (union_subset p q) u
  apply Six.descend K W (A₊ S) (A₊ T) X J hp (union_subset (wingspan_mono p) (wingspan_mono q)) (P.history.circuit.supports s he).1
  intro x
  let Q:=bipocket ((K).c J) W (Satin.region (A₊ S) ((K).c J)) (Satin.region (A₊ T) ((K).c J))
  apply Q.closed_of_finiteDimensional.mem_of_tendsto (P.block_hist s D _ he J x)
  filter_upwards [ht.eventually (turning Y H (s+1) X), P.history.finance (s+1)] with i v e
  have hs:= P.block_charged W S T D s p q u (i:=r i) (k:=m i) (show legalAt Y s (r i) (m i) from ⟨e.depth, e.enters⟩) v
  exact dressedMatrix K W _ _ _ hs J x
lemma vol_mono (n:ℕ): Monotone (volumeAround P.par P.width n):= by
  induction n with
  | zero => exact fun i j e=>e
  | succ n h=> exact fun i j e=> wingspan_mono (h e)
/-- The two particular pockets, NOT the full charged support D. -/
lemma onward (F:P.Test)(p:S⊆D)(q:T⊆D)(h:F.val∈ DressedPair K W S T D)(n:ℕ) :
    (P.conveying s n F).val∈ DressedPair K W (volumeAround P.par P.width n S) (volumeAround P.par P.width n T) (volumeAround P.par P.width n D):= by
  induction n with
  | zero => exact h
  | succ n u=> exact P.advance_charged _ _ _ _ (s+n) (P.vol_mono n p) (P.vol_mono n q) u
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
