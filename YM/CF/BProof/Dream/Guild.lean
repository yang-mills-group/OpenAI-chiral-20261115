import YM.CF.BProof.Dream.Whirl
import YM.CF.Matter.Rep
/-! Blocks preserve angle sums, unit tests. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Function SU Join Finset
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {I J: Type*} [Fintype I][DecidableEq I][Fintype J][DecidableEq J]
local notation "D" =>Matrix.diagonal
abbrev atlas (f:I≃J): Op I ≃ₐ[ℂ] Op J:= reindexAlgEquiv ℂ ℂ f
lemma atlas_det (f:I≃J)(A:Op I): (atlas f A).det=A.det:=det_reindex_self ..
lemma atlas_star (f:I≃J)(A:Op I): (atlas f (star A))=star (atlas f A):= rfl
lemma atlas_trans (f:I≃J)(A:Op I): (atlas f (Aᵀ))=(atlas f A)ᵀ:= rfl
lemma atlasU (f:I≃J){A:Op I}(h:A ∈ unitary (Op I)): atlas f A ∈ unitary (Op J):=by constructor <;> rw [←atlas_star,← map_mul] <;> first | rw [h.1, map_one] | rw [h.2,map_one]
lemma whirlAt(f:I≃J){A:Op I}{m:ℝ}(h:Whirl A m) : Whirl (atlas f A) m:=by
 obtain ⟨U,d,h,e,v⟩:=h; subst A; refine ⟨⟨atlas f U.val,atlasU f U.property⟩,d ∘ f.symm,?_,fun i=>e _,(Equiv.sum_comp f.symm d).trans v⟩; rw [dial_eq,dial_eq,map_mul,map_mul,atlas_star]; congr 2; ext i j; change diagonal (rose ∘ d) (f.symm i) (f.symm j)=_; by_cases h:i=j <;> simp [h] -- tune

abbrev choir (A:I→Op J):Op (I × J):= jump (Equiv.refl _) A
lemma choir_mul (A B:I→Op J): choir A*choir B=choir (A*B):= jump_mul ..
lemma choirU (A:I→Op J)(h:∀ i,A i∈ unitary (Op J)) : choir A∈ unitary (Op (I×J)):=jump_unitary _ _ h
lemma choir_star (A:I→Op J): star (choir A)=choir (star A):= jump_star ..
lemma choir_trans (A:I→Op J): (choir A)ᵀ=choir fun i=>(A i)ᵀ:=by ext ⟨i,b⟩ ⟨j,c⟩; simp only [transpose_apply,jump_apply,Equiv.refl_apply,choir]; by_cases h:i=j <;> simp [h, Ne.symm]
lemma choir_det (A:I→Op J): (choir A).det=∏ i, (A i).det:=by
 let f:=Equiv.prodComm J I; rw [show choir A= Matrix.reindex f f (Matrix.blockDiagonal A) from ?_,det_reindex_self,det_blockDiagonal]; ext ⟨i,b⟩ ⟨j,c⟩; by_cases h:i=j <;> simp [choir,jump_apply, Matrix.reindex_apply,Matrix.blockDiagonal,f,h]
lemma whirlChoir (A:I→Op J) (m:I→ℝ)(p:∀ i,Whirl (A i) (m i)) : Whirl (choir A) (∑ i,m i):=by
 choose U d hu e h using p; let V(i):=(U i).val; let W:UNI (I × J):=⟨choir V, choirU _ (fun i=>(U i).property)⟩
 refine ⟨W,uncurry d,?_,fun i=>e _ _,(Eq.trans (Fintype.sum_prod_type ..) (sum_congr rfl fun i _=> h i))⟩
 have he:D (rose ∘ uncurry d)=choir (fun i=>D (rose ∘ d i)):=by ext ⟨i,b⟩ ⟨j,c⟩; by_cases h:i=j; subst j; by_cases t:b=c <;> simp [t,choir,jump_apply]; simp [h, choir,jump_apply]
 rw [dial_eq,he,show W.val=choir V from rfl,choir_star,choir_mul,choir_mul]; apply congrArg; funext i; exact (hu i).trans (dial_eq ..)
lemma both_trans (A: Op I) (B: Op J) : (both A B)ᵀ=both Aᵀ Bᵀ := by simp [both,Matrix.fromBlocks_transpose]
lemma whirlJoin {A: Op I}{B: Op J}{m v:ℝ}(h:Whirl A m)(g:Whirl B v) : Whirl (both A B) (m+v):=by
 obtain ⟨U,d,rfl,h,u⟩:=h; obtain ⟨V,e,rfl,g,v⟩:=g; let W:UNI (I⊕J) := ⟨both U.val V.val,both_unitary U.property V.property⟩
 refine ⟨W,Sum.elim d e,?_,fun x=> Sum.casesOn x h g ,?_⟩ -- tune sum.elim
 · have ht:D (rose ∘ Sum.elim d e)=both (D (rose ∘ d)) (D (rose ∘ e)) := by
      ext i j; rcases i with i|i <;> rcases j with j|j <;> simp [both, diagonal_apply]
   rw [dial_eq,dial_eq,dial_eq,ht,show W.val=both U.val V.val from rfl,star_both,both_mul,both_mul]
 rw [Fintype.sum_sum_type]; exact congrArg₂ _ u v
lemma copyWhirl {A:Op I}{m:ℝ}(h:Whirl A m): Whirl ((1:Op J)⊗ₖ A) (Fintype.card J*m):=by
 rw [← jump_replicate]; refine (Eq.mp ?_ (whirlChoir (fun _:J=> A) (fun _=>m) (fun _=>h))) -- tune
 congr 1; simp
lemma scalarWhirl(t:ℝ)(e:MainT t) : Whirl (rose t • (1:Op I)) (t*Fintype.card I):= by
 refine ⟨1,fun _=>t,?_,fun _=>e,by simp [mul_comm]⟩; rw [dial_eq]; ext i j; by_cases h:i=j <;> simp [h]
end YM.CF.BProof.Dream
