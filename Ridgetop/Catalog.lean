import Mathlib
set_option autoImplicit false
noncomputable section
namespace Factory
open WithLp Function Finset Matrix Submodule LinearMap
open scoped Topology Matrix RealInnerProductSpace BigOperators Classical
variable {I Z:Type*}[Fintype I][Fintype Z]
local notation "E" I=>EuclideanSpace ℝ I
lemma tea (A:Matrix I I ℝ)(B:A.transpose=A){v:I→ℝ}(g:∀ u:I→ℝ,A*ᵥu=0→dotProduct v u=0):∃ t:I→ℝ,A*ᵥt=v:=by
 classical
 let p:(EuclideanSpace ℝ I) →ₗ[ℝ] (EuclideanSpace ℝ I):=toLpLin 2 2 A
 have H : toLp 2 v ∈ LinearMap.range p:=by
    rw [← Submodule.orthogonal_orthogonal (K:=LinearMap.range p)]
    intro z hz; let u:I→ℝ:=ofLp z
    have hA: A *ᵥ u=0 :=by
       apply funext; intro i
       let y:I→ℝ:=Pi.single i 1
       have he : inner ℝ (p (toLp 2 y)) z=0:=hz _ ⟨_,rfl⟩
       change inner ℝ (toLp 2 (A*ᵥ y)) (toLp 2 u)=0 at he; rw [EuclideanSpace.inner_toLp_toLp,star_trivial,←B,dotProduct_transpose_mulVec] at he
       simpa [y] using he
    change inner ℝ (toLp 2 u) (toLp 2 v)=0; rw [EuclideanSpace.inner_toLp_toLp,star_trivial,g _ hA]
 obtain ⟨x,hx⟩:=H; exact ⟨ofLp x,congrArg ofLp hx⟩
lemma milk (A:Matrix I Z ℝ)(M:Matrix I I ℝ)(B:M.transpose=M){c:ℝ}(p:0<c)(q:∀ i:I→ℝ,c*dotProduct i i≤dotProduct i (M*ᵥi))(v:I→ℝ): ∃ u:Z→ℝ,(A.transpose*M*A)*ᵥu=A.transpose*ᵥ v:= by
 apply tea _ (by rw [Matrix.transpose_mul,Matrix.transpose_mul,B,Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]); intro i hi
 have hs:=q (A*ᵥi)
 rw [← mulVec_mulVec,← mulVec_mulVec] at hi
 -- select M RHS by dot symmetry
 let k:= M *ᵥ A *ᵥ i
 have he:dotProduct (A*ᵥi) k=0:=by rw [dotProduct_comm, ←dotProduct_transpose_mulVec A]; unfold k; rw [hi,dotProduct_zero]
 rw [he] at hs
 -- infer A*ᵥ i=0 dot lemma
 have hp:dotProduct (A*ᵥ i) (A*ᵥi) ≤0:= nonpos_of_mul_nonpos_right hs p
 have hu:A*ᵥi=0 :=by
    exact dotProduct_self_eq_zero.mp (le_antisymm hp (by unfold dotProduct; exact sum_nonneg (fun _ _=> mul_self_nonneg _)))
 rw [dotProduct_comm,dotProduct_transpose_mulVec,hu,dotProduct_zero]
#print axioms milk
#check dotProduct_self_eq_zero
#check dotProduct_single_one
end Factory
