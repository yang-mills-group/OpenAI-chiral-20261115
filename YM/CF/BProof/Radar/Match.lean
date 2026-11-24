import YM.CF.BProof.Radar.Penny
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 4000
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard Rows
open scoped BigOperators Classical
variable {n:Side}{l k r d:ℕ}{C A V U:Type*}
namespace Policy
abbrev Joint(X:Field n A V)(Y:Field n A U):Field n A (V×U):=fun i j=>(X i j,Y i j)
lemma dawn(X:Field n A V)(Y:Field n A U): Uses (Joint X Y) X d∧ Uses (Joint X Y) Y d :=⟨fun i x y H=>congrArg Prod.fst (Uses.self i x y H),fun i x y H=>congrArg Prod.snd (Uses.self i x y H)⟩
lemma day(X:Field n A V)(Y:Field n A U): Loyal (Joint X Y) X∧ Loyal (Joint X Y) Y:= ⟨fun s i E t u v=>congrArg Prod.fst (t u v), fun s i E t u v=>congrArg Prod.snd (t u v)⟩
variable {m b:ℕ}
namespace Viewport
variable (τ k :ℕ) -- parser k shadows remove
end Viewport
/- f: Hue full plate, ℱ:ingredient field.Controls staged recur at range.Use will evaluate lookup weights via Ranker later. -/
variable (l:ℕ)
variable (f:Field n A V)(Z:C)(Ψ:ℕ→ Field n A C →Field n A C)
def stage :ℕ→Field n A C
 | 0=> fun _ _=> Z
 | k+1=> Ψ k (stage k)
lemma stage_uses(p:∀ i (X:Field n A C), Uses (Joint f X) (Ψ i X) l)(k:ℕ): Uses f (stage Z Ψ k) (k*l):=by
 induction k with | zero=> intro i a b h; rfl| succ k ih=> rw [stage,Nat.succ_mul, add_comm]; exact (Uses.self (f:=f)).comm ih |>.thenL (p k _)
lemma Loyal.self:Loyal f f:= fun i p E h=>h
lemma stageL(p:∀ i (X:Field n A C), Loyal (Joint f X) (Ψ i X))(k:ℕ): Loyal f (stage Z Ψ k):=by
 induction k with|zero=> intro i q E F i j; rfl|succ k ih=> rw [stage]; intro i q E t; exact p _ _ _ _ _ ((Mesh.Loyal.meet (f:=f) (Loyal.self f) ih) i q E t) -- namespace
-- tune namespace Loyalty introduced as Policy.Loyal collides. 
end Policy
end YM.CF.BProof.Mesh
