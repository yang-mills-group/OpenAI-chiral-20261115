import YM.CF.Esti.Cap
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {V':E→ Config G c}{U':E→ Config G f}
lemma agree_face {n:Side}(V W:Config G n)(s: Signed)(i:Face (Per n))(p:∀ j: Edge (Site n), j.1 ∈ (touched i) ∧ j.1+ Lattice.step j.2∈touched i→ V (sendEdge s 0 j)=W (sendEdge s 0 j)) : faceValue (pull s 0 V) i=faceValue (pull s 0 W) i:=travel_local _ _ (pull s 0 V) (pull s 0 W) (fun j k l=>pass_link (p j ⟨List.mem_toFinset.mpr k, List.mem_toFinset.mpr l⟩)) -- tune ambiguity
lemma faceT (z:Signed)(i:Cell c)(j:Bond c)(p: pinPos j⊆ touched i):pinPos (sendEdge z 0 j) ⊆ touched (Face.send z 0 i):=by rw [pinPos_turn,Work.H03.touched_send]; rw [show affine z (0:Site c)=fun p=>z.act p from funext fun p=> add_zero _]; exact image_subset_image p
lemma face_h (p:∀ᶠ i in 𝓝 x',Agrees (halo 15 A.flags) (V' i) (V' x')) (z:Signed): HeldT (pull z 0 ∘ V') (traceZ (turnStore z A).flags) x':=by
 filter_upwards [p] with i p j v; have he:(j.1)∈(turnStore z A).flags:= (mem_filter.mp v).2; have hv:(z.act j.1)∈A.flags:=(flag_turn ..).mp he
 apply agree_face (V' i) (V' x') z; intro k t; have h:= insert_subset_iff.mpr ⟨t.1, singleton_subset_iff.mpr t.2⟩; have hx : touched (Face.send z 0 j)⊆halo 15 A.flags:=by
    rw [Work.H03.touched_send]; intro p H; obtain ⟨p,h,rfl⟩:=mem_image.mp H; have hm':separation (z.act j.1) (affine z 0 p) ≤ 15:=by unfold affine; rw [add_zero,separation_signed]; exact (Work.E01.sep_touched j p h).trans (by norm_num)
    exact halo_spec.mpr ⟨_,hv,hm'⟩ -- tune semis
 have he:= Finset.Subset.trans (faceT z j k h) hx
 exact p _ (he (mem_insert_self ..)) (he (mem_insert_of_mem (mem_singleton_self _)))
variable {F:Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{fE:E→ Prices G (Active A x F)}
abbrev treeF(z:LinkArray SU.group (Frozen A x F))(V:E→ Config G c)(R:E→ Prices G (Active A x F))(i:E):= landed x A F (V i) z (R i)
lemma bareH {i:Bond f}(a b:E)(p:¬ ∃ j:Active A x F,j.val.val=i):treeF Y V' fE a i=treeF Y V' fE b i:=by
 by_cases h:i∈F.trunks; · change F.drape _ _= F.drape _ _; rw [F.on_tree _ ⟨i,h⟩,F.on_tree _ ⟨i,h⟩] -- tune
 let z:F.Free:= ⟨i,h⟩; by_cases j:chill A x F z
 · let t:Frozen A x F:=⟨z,j⟩; exact (held_physical x A F _ _ (fE a) t).trans (held_physical x A F _ _ (fE b) t).symm
 exact False.elim (p ⟨⟨z,j⟩,rfl⟩)
lemma pileD(hp:shovel S.patch+10 ≤ radiusB x): Frolic A x (treeF (F:=F) Y V' fE) x':= pervert A _ (F:=F) (Eventually.of_forall fun i j h=>bareH x' i (fun ⟨_,v⟩=>h ⟨_,v.symm⟩)) hp
lemma tide_d (z:Signed): HeldT (pull z 0∘treeF (F:=F) Y V' fE) (turnStore z A).costs x':=by
 apply Eventually.of_forall; intro i p y; apply agree_face (treeF Y V' fE i) (treeF Y V' fE x') z; intro j k; let Z:= sendEdge z 0 j
 have ht:Z.1∈ touched (Face.send z 0 p):= faceT z p j (insert_subset_iff.mpr ⟨k.1,singleton_subset_iff.mpr k.2⟩) (mem_insert_self ..)
 have he:S.ratio.parent Z.1∈ A.place:=mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨_, (costs_turn ..).mp y, mem_image_of_mem _ ht⟩))
 exact bareH i x' (fun ⟨i,h⟩=> remote i (by rw [h]; exact halo_subset _ _ he))
end YM.CF.Esti
