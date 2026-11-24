import YM.CF.DPress.Chess.Lift.Charm
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Rush Scroll Tulip Lat Peaks Cube Dial SU Branch Wilson Fock Fixed NormedSpace Spire Scree Skye Tap Reed Print
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n m L:Side}{G:Ratio n m}{M: Male}{j r:ℕ}{o: Odd L.val}{Q:Op Slot}
lemma PrintU.pay {b:Bool}{X: Type*}{S:CoverS m}(D: Finset X){f:X→ReOp n}{g:X→WaveK n m}(h:∀ i,PrintU G M j Q S b (f i) (g i)): PrintU G M j Q S b (∑ i∈D,f i) (∑ i∈D,g i):=by induction D using Finset.induction_on with|empty=> rw [sum_empty,sum_empty]; apply PrintU.zero|insert i S p ih=> simp only [sum_insert p]; exact (h i).add ih
-- global specialized stage.F.Signal. continuous linear lift. Does not need multiplicativity over distinct decompositions (carry first, then the other separately). maintain semantics.
structure Tide (j:ℕ)(M:Male)(G:Ratio n m)(r:ℕ)(Q:Op Slot) (S:CoverS n) where
 F: Nom n m → (ReOp n →L[ℂ] ReOp m)
 nature: Continuous F
 issue : ∀ X,RefineE S false X→ PrintU G M j Q (spreadB G S r) false X (fun i=> F i X)
lemma tide (p: Odd G.count.val)(t:∀ i:Male,Symbol.Stroke G (pulse G j i) r)(h:star Q=Q)(S:CoverS n): Nonempty (Tide j M G r Q S):=by
 let W:= Print.spaceE (Fixed.upperIndices n) (matterRegion n S) false; obtain ⟨N,f,g,l⟩:= Print.linear_basis W; choose Fv v using fun i:Fin N=> shipB G M j Q p t h (b:=false) (S:=S) (g i).val (show RefineE _ false _ from (g i).property); let F(A:Nom n m):ReOp n→L[ℂ] ReOp m := ∑ i:Fin N,(f i).smulRight (Fv i A); refine ⟨F,?_,?_⟩
 · apply continuous_finsetSum; intro i _; exact ((ContinuousLinearMap.smulRightL ℂ (ReOp n) (ReOp m) (f i)).continuous.comp (v i).contF) -- no lemma?
 intro X t; rw [show (fun i=>F i X)=∑ i,f i X • Fv i from ?_]; swap; · funext i; unfold F; simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,Finset.sum_apply]; rfl
 conv=> arg 7; rw [l X t] -- syntax? parameters explicit S?, trace
 exact PrintU.pay _ (fun i:Fin N=>(v i).color (f i X))
end YM.CF.DPress.Chess.Lift
