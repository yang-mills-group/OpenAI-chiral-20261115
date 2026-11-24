import SatinFixedContrastNovember4
import YM.SU5.Thin.Compound

set_option autoImplicit false
set_option maxHeartbeats 170000
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
open Sifter DoseBill Theatre
namespace VoucherOp
lemma fieldAskedAdd (P:Spine)(A:Set Vantage)(t:ℕ)(x y:P.Test)(h:P.asked_at t x A)(g:P.asked_at t y A) :
    P.asked_at t (x+y) A:=by
  obtain ⟨S,p,r⟩:= h; obtain ⟨T,u,v⟩:= g; refine ⟨S∪T, Subalgebra.add_mem _ (tallerBay _ _ _ Finset.subset_union_left p) (tallerBay _ _ _ Finset.subset_union_right u),?_⟩
  rw [P.pin_union]; exact Set.union_subset r v
lemma fieldAskedScoop (P:Spine)(A:Set Vantage)(t:ℕ)(D:Scoop) (x:ℕ→P.Test)(h:∀ i∈D.take,P.asked_at t (x i) A) : P.asked_at t (D.recipe x) A:=by
  suffices h:∀ (S:Finset ℕ)(w:∀ i∈ S,P.asked_at t (x i) A),P.asked_at t (∑ i∈S, (D.weight i:ℂ) • x i) A from h D.take ‹_›
  intro S p; induction S using Finset.induction_on with
  | empty=> rw [sum_empty]; exact ⟨∅,(bay _ _ _).zero_mem,by simp [pinFoot]⟩
  | @insert i S x' ih=>
    obtain ⟨A,u,y⟩:= p i (Finset.mem_insert_self ..); rw [sum_insert x']; exact fieldAskedAdd P _ t _ _ ⟨A,(bay _ _ _).smul_mem u _, y⟩ (ih (fun j b=> p j (Finset.mem_insert_of_mem b)))
variable {P:Spine}{x:P.Spectrum0 3}{n:ℕ}{b:ℕ→ℕ}{Z:Lead.Clan} (A:P.VoucherOp x Z n b) (d:Bool)(F:SampleDose)
local notation "L" i:max=> P.cardSchedule Z n (b i) d
lemma isObserved (s t:ℕ)(k:Cover) : A.formMark d s t k∈ enclave P.calibration∧ A.markField d s t F∈ enclave P.calibration :=
  ⟨Subalgebra.sum_mem _ fun i _=> Subalgebra.smul_mem _ (P.issuing_color t k (L (s+i))) _, Subalgebra.sum_mem _ fun i _=> Subalgebra.smul_mem _ (P.prepared_color t (L (s+i)) F) _⟩ -- tune unfolds
lemma shrink (ε:ℝ)(p:0<ε) : ∀ᶠ s:ℕ in atTop, ∀ t:ℕ,A.eligible s t →
    (∀ j:ℕ,∀ k:Axis,(P.cardSchedule Z n (b (s+j)) d).realWidth P k <ε) ∧
    ∀ k:Cover, P.asked_at t (A.formMark d s t k) (Metric.ball (P.meshPose t k) ε):= by
  obtain ⟨N,v⟩:= eventually_atTop.mp (Filter.eventually_all.mpr (fun i:Axis=> ((P.probeWidth_static n i).comp A.safe.tendsto_atTop).eventually (gt_mem_nhds p)))
  filter_upwards [eventually_ge_atTop N] with i u t ti
  have g(j:ℕ)(k:Axis) : (L (i+j)).realWidth P k< ε:= (P.schedule_width Z n _ k d).trans_lt (v (i+j) (by omega) k)
  refine ⟨g,fun k=> fieldAskedScoop _ _ _ _ _ (fun j w=>?_ )⟩ -- metas
  obtain ⟨_,B,h⟩:= P.thinStage_support (L (i+j)) ε p (g j) t ((P.schedule_height ..).trans_le (ti j w)) k
  exact ⟨P.plotSet t _ k, B,h⟩
lemma dwellings (V:Doorway)(p:tsupport F.val ⊆ V.spare.invites) :
    ∀ᶠ s:ℕ in atTop, (∀ j:ℕ,P.spacePrice (P.cardSchedule Z n (b (s+j)) d) F⊆ V.invites) ∧
      ∀ t:ℕ,A.eligible s t→ P.asked_at t (A.markField d s t F) V.invites := by
  obtain ⟨N,x⟩:= eventually_atTop.mp (V.spareCosts (fun i k=>(L i).realWidth P k) (fun k=> ((P.probeWidth_static n k).comp A.safe.tendsto_atTop).congr fun i=> (P.schedule_width Z n _ k d).symm))
  filter_upwards [eventually_ge_atTop N] with i u
  have hx(j:ℕ):P.spacePrice (L (i+j)) F⊆ V.invites:= bounded_within (L _) F p (x (i+j) (by omega))
  refine ⟨hx,fun t q=> fieldAskedScoop _ _ _ _ _ (fun j w=>?_)⟩
  obtain ⟨S,t,h⟩:= P.prepared_at t (L (i+j)) F ((P.schedule_height ..).trans_le (q _ w)); exact ⟨S,t,h.trans (hx _)⟩
end VoucherOp
#print axioms VoucherOp.shrink
#print axioms VoucherOp.dwellings
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
