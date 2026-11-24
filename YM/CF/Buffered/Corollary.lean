import YM.CF.Buffered.Cone
import YM.CF.Buffered.Operator
import YM.CF.Buffered.Application

/-!
# Import this for the corollary

User-facing checkpoint: `Corollary.positive`, `.form`, `.matrix` (Form.lean)
and `.output` (Application.lean). Cone collects the actual price proof. Here
include some consequences and scope checks/variants. See `the construction notes`
for dependency details.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
attribute [local instance] opCStarAlgebra
section Finite
variable {K : Calibration} (P : Histories K) {wide : Bool}
/-- It suffices in the proof to advance each input with its own support,
using the linear-combination closure of `Eligible`. Can also take together
on finite volumes. Every finite list fits at sufficiently large fixed period,
without shrinking the margin. Can take all its linear combinations there. -/
lemma Corollary.list {I : Type*} [Fintype I] (F : I → eligible K wide) :
 ∃ S : Finset Cover, goodSet K S ∧ (∀ i,InTest K wide S false (F i).val) ∧
   (∀ c:I→ℂ, InTest K wide S false (∑ i,c i • (F i).val)) ∧
   ∀ᶠ m in atTop, Set.InjOn (wrap (More (K.c m))) (↑S : Set Cover) ∧ allocated K m S ∧ S.image (wrap (More (K.c m))) ⊆ K.fits m := by
 choose f u ht using fun i=>(show Eligible K wide (F i).val from (F i).property).support
 let S:= univ.biUnion f; have hg(i):=InTest.mono (u i) (subset_biUnion_of_mem f (mem_univ i))
 have hp : goodSet K S := by intro i v; obtain ⟨x,_,t⟩:= mem_biUnion.mp v; exact ht x i t
 exact ⟨S,hp,hg, fun c=> InTest.sum univ _ (fun i _=>InTest.smul _ (hg i)),(separates K S).and ((allocates K S).and (fits_eventually K S hp))⟩
-- scope: literal CapP at each top with shared numerical shoot,
-- regulator identity, partition nonzero sharp, donor *strict*
lemma Corollary.cuts : ∀ᶠ n in atTop, ∀ m:Side, K.Allowed m n →
   (let X:= P.sharp m n n
    ∀ j:Orbit (cell m K.B K.R.L n), denZ X K.P (P.loom m n) j= Vale.capP K.P X.beta (K.T.a n) j.1) ∧
   (∀ j≤n, partitionZ (P.sharp m n j) K.P (P.loom m j)≠0) ∧
   0 < partitionZ (P.warm m n 0) K.P (P.loom m 0) := by
 filter_upwards [P.paid,pc_low P] with n t p; intro m a; have h:= t m a
 let g:= h.1
 have he : partitionZ (P.sharp m n 0) K.P (P.loom m 0) ≠ 0 := part_ne_zero _ _ _ (norm_pos_iff.mp ((half_pos (Real.exp_pos _)).trans_le (p m a)))
 refine ⟨fun j=> g.cap_density K.clip j, fun j u=> by rw [g.sharp.balance j u,←g.sharp.balance 0 (Nat.zero_le _)]; exact he, strictDonor K.P _ (P.loom m) K.η K.J.d n (P.wave' n) (steps K.V m K.B n) 3 K.legal K.R.coarse g.warm_grant (fun j _=> P.lawn m a.1 j) K.buffer K.ζ g.heat.choose ?_⟩
 exact part_ne_zero _ _ _ (norm_pos_iff.mp ((Real.exp_pos _).trans_le h.2.2))
end Finite
section read
variable (K : Calibration)
open Bilinear
-- scope check for the mark across large periods: the literal un-rephased formula
-- used in the ms when vertex + 1 < c. always so eventually.
lemma unpack_word {m:Side} (h : K.vertex + 1 < (K.c m).val) (V : Fields (K.c m)) :
 word K m V = - ((K.vertex:ℂ)^3/5) • ∑ p∈ five, ∑ q∈ five,
 (matter (travel V.1 (node (wrap (K.c m) creatorSite)) (segment K))).val p q •
   (takeF (Lifted.index (K.c m) (removerSite K) 2 q)*put (Lifted.index (K.c m) creatorSite 0 p)) := by
 let N:=K.c m
 have ht(x:Cover) (p : ∀ i:Axis, 0 ≤ x i ∧ x i < N.val) : ∀ b c, basisC N x b c=basisKet (Lifted.index N x b c) := by
   have he: periods N x= 0 := funext fun i=> Int.ediv_eq_zero_of_lt (p i).1 (p i).2
   intro b c; simp [basisC,Lifted.winding,he,fee]
 have hy:(↑(mesh m K.R.L 0).val:ℤ)*2*↑K.B.val> (K.vertex:ℤ)+1 := by exact_mod_cast h
 have hh := ht creatorSite (fun i=> by simp [creatorSite,N,Calibration.c] ; omega); have hi:= ht (removerSite K) (fun i=> by unfold N; by_cases t:i=3 <;> simp [removerSite, creatorSite,t]  <;> omega)
 have hz: onC N V.1=expandAt 0 V.1:= rfl
 unfold word; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.mul_apply]; refine congrArg (- ((K.vertex:ℂ)^3/5) • ·) (sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_)
 change (D5 K i j (onC N V.1)) • (1 : FC _)*(Fock.remove _ * create _) = _; rw [Algebra.smul_mul_assoc,one_mul, hh,hi, Fock.remove,create_put,create_put]; unfold D5; rw [hz,travel_at,add_zero,node_of]

lemma cuts_word : ∀ᶠ m:Side in atTop,K.vertex+1 < (K.c m).val := (c_grows K).eventually (eventually_gt_atTop _)
end read
section alternative
variable {wide : Bool} {K : Calibration} (P : Comparisons K) (C : Process K)
-- not assuming CapP-vs-Heat rec-delta in this version (use the budget
-- estimate of p-delt instead)
variable {E : Family K→ℂ} (h : Settled P.hist C wide E)
include h
theorem Corollary.gram_full {I : Type*} [Fintype I] (F : I→eligible K wide) : E 1=1 ∧
 Matrix.PosSemidef (Matrix.of (fun i j=> E (thetaK K (F i).val*(F j).val))) := ⟨h.value,matrix P.hist _ h F⟩
end alternative
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Corollary.gram_full
#print axioms YM.CF.Buffered.unpack_word
#print axioms YM.CF.Buffered.Corollary.output
#print axioms YM.CF.Buffered.Corollary.cuts
#print axioms YM.CF.Buffered.Corollary.list
