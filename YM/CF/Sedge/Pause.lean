import YM.CF.Sedge.Winnow
/-! Orientation under relabel. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n m: Type*} [LinearOrder n][LinearOrder m][Fintype n][Fintype m]
variable (G:n≃ m)
def cartsL (x: Wave n): Wave m:= hoist G.toEmbedding ∅ x
def portW (P: Op n):Op m:= P.submatrix G.symm G.symm
lemma flexL (P:Op n): addS G.toEmbedding ∅ P=portW G P:=by
  rw [addS,show cutM (∅:Finset m)=0 from by ext i j; simp [cutM,Matrix.diagonal_apply],zero_add]
  ext i j; obtain ⟨i,rfl⟩:=G.surjective i; obtain ⟨j,rfl⟩:=G.surjective j; exact (desk_at G.toEmbedding P i j).trans (by simp [portW])
lemma shelfG: Deck G.toEmbedding ∅:= ⟨by simp⟩
lemma roofS:lows G.toEmbedding=univ:=by ext1 i; obtain ⟨i,rfl⟩:=G.surjective i; simp only [mem_univ,iff_true]; exact coil_hit ..
lemma relabelF {C P:Op n}(h:Cᵀ= -C)(p:IsStarProjection P):filled (portW G P) (portW G C)=cartsL G (filled P C):=by
  let f:=G.toEmbedding; let S:=portW G C; let s:Finset m:=∅
  have hs: Sᵀ= -S:=Matrix.ext fun i j=> Matrix.ext_iff.mpr h (G.symm i) (G.symm j)
  rw [← flexL G P,crane _ _ (shelfG ..) _ hs _ p,pf,paired_vac,one_smul]; swap
  · rw [roofS,show cutM (univ:Finset m)=1 by ext i j; simp [cutM,Matrix.diagonal_apply,Matrix.one_apply]]; exact Commute.one_left _
  rw [show summit f S=C by ext; simp [summit,f,S,portW]]; rfl
lemma carts_s (p: Wave n)(c:ℂ):cartsL G (c • p)= c • cartsL G p:=map_smul ..
lemma carts_n (p:Wave n): ‖cartsL G p‖=‖p‖:=hoistN _ _ (shelfG G) _
lemma carts_p {P: Op n}(p:IsStarProjection P): IsStarProjection (portW G P):= flexL G P ▸ projectorD _ _ p (shelfG G)
lemma carts_sea {P:Op n}{v: Wave n}(p:IsStarProjection P)(e:Sea P v): Sea (portW G P) (cartsL G v):= flexL G P ▸ stageUp _ _ (shelfG G) p e
lemma carts_inj:Function.Injective (cartsL G):=Function.LeftInverse.injective (pourL _ _ (shelfG G))
end YM.CF.Fock
