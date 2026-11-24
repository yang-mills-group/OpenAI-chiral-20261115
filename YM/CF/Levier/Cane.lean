import YM.CF.Levier.Acro
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
lemma chron(W: Toll (Iota G)) (x y:Iota G): chase G k W y x= chase G k (Function.swap W) x y:=by unfold chase; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold scene; dsimp only; rw [norm_mul,norm_mul,norm_star,norm_star,mul_comm ‖_‖]
include h
variable {T:NoteS G e}
lemma Bisca.stay(hp:Bisca G e t v d p T): Bisca G e t v d (population*p) (coda G e k T):=by
 obtain ⟨C,l,u⟩:=hp; have hf:Sweep N:=k; have hg(S):= pivot G h e k S _ _ t v (l S); let M:= wheelS G k C; have he: ∀ i,Suite (badge _) (pinH G e t) (pinH G e v) i (M i) (coda G e k T i):=by intro i; unfold coda M wheelS; have H:=hg (toRoar G k⁻¹ i); rw [wish_inv G h] at H; exact H
 have hy:u.posP=u.posP:=rfl
 have hv(W:Seal (Site (More P))→ Toll κ)(q:Ledger d W p)(g:∀ S i j, 0≤W S i j)(i:κ): ∑ j:κ,saleM d (wheelS G k W) i j≤population*p:=by
    have ht:=spoke G h e k W 0 0 d p (fun i=>by simpa only [pow_zero, one_mul] using q.rows i) g le_rfl i; simpa only [pow_zero,one_mul] using ht
 refine ⟨M,he, mul_nonneg (show 0≤population by unfold population; positivity) u.posP,hv C u (fun i=> (l i).nonn),fun i=>?_⟩; have hp(j):saleM d M j i = saleM d (wheelS G k (fun i=>Function.swap (C i))) i j:=by unfold M saleM wheelS; simp_rw [chron G k _ i j]
 simp_rw [hp]; exact hv _ u.flip (fun S i j=>(l S).nonn j i) i
omit h
variable {G e}
lemma Bisca.sum {X: Type*}(s:Finset X)(C:X→NoteS G e)(w:X→ℝ)(h:∀ i∈s,Bisca G e t v d (w i) (C i)): Bisca G e t v d (∑ i∈s,w i) (fun S x=>∑ i∈s,C i S x):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; refine ⟨_,fun S=> Suite.free _,le_rfl,fun i=>?_,fun i=>?_⟩ <;>simp [saleM]
 | @insert i s v ih=> simp only [sum_insert v]; exact (h i (mem_insert_self ..)).plusK (ih fun j k=> h j (mem_insert_of_mem k)) -- tune
variable (G e)
include h
lemma serene_p {I:Type*}(T:I→NoteS G e)(π:I→Bool→I)(p:∀ i, Bisca G e t v d r (T i))(i:I): Bisca G e t v d (population*r) (ced G e π T i):=by
 unfold ced; have he : population*r= ‖pic (N:=N)‖*(∑ _k:Sweep N,population*r):=by simp only [pic,Complex.norm_real,norm_inv,Real.norm_natCast,sum_const,nsmul_eq_mul,card_univ,←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=Sweep N): (Fintype.card (Sweep N):ℝ)≠0),one_mul]
 rw [he]; exact Bisca.sm (pic (N:=N)) (Bisca.sum univ (fun k=> modeT G e k π T i) _ fun k _=>Bisca.stay G h e k (p _))
end YM.CF.Levier
