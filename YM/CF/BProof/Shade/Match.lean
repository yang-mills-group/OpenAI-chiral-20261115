import YM.CF.BProof.Shade.Act
import YM.CF.BProof.Shore.Quiz
/-! Covariance before averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Nest Stave Gallery Function MeasureTheory Metric Filter Finset Wilson Lattice
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
variable {T:Tray (Floor q) ε}{F:Drum (rollup q T) (Floor q)} {A A':Score n q} {R R':StampB n}
variable {U V:Heads n}(W:Writ q T s l u a b δ d θ F) (B:Seal A s l b a)
local notation "P_"=>make s l u T F
abbrev RevB (k:Bool)(p:Bool)(z:Bool×Bool): Bool×Bool:= (k.xor z.1,p.xor z.2)
def edge_h (j:Signed)(x:Site n)(p:Bool)(R R':StampB n):Prop:=∀ i:Bones n,R i=RevB (j.flip i.2) p (R' (sendEdge j x i))
variable (j:Signed)(x:Site n)(p:Bool)
local notation "G"=>facet j x
local notation "O"=>Opts j x p
local notation "ακ"=>Spire.polarT p
-- easier formula.Step.read make similar oriented both.Step.neg uses inverse.
private def ticket (R:StampB n)(d:Step)(x:Site n):Bool×Bool:= RevB d.neg false (R (d.used x))
private lemma fare (R:StampB n)(A:Score n q)(T:Tray (Floor q) ε)(F:Drum (rollup q T) (Floor q))(U:Heads n)(x:Site n)(i:Step): i.read (make s l u T F A R U) x=if caught s l u A U x∧caught s l u A U (x+i.vec) then i.read U x else decideG (ticket R i x) (opened s l u T F A U x) (opened s l u T F A U (x+i.vec)):=by
 -- notation P_ might refers section T ignored shadow; explicit.S Lean
 cases i with
 | mk i neg=>
    cases neg
    · change (make s l u _ _ _ R _) (x,i)=_; unfold make ticket RevB; dsimp only; rw [Bool.false_xor, Bool.false_xor]; rfl
    let y:= x-step i; change (((make _ _ _ _ _ _ _ _) (x-step i,i))⁻¹)=if caught s l u A U x ∧ caught s l u A U (x+ -step i) then (U (x-step i,i))⁻¹ else _; unfold make ticket
    dsimp only; simp only [Step.vec,↓reduceIte,← sub_eq_add_neg, sub_add_cancel]; split; · rename_i h; rw [if_pos (⟨h.2,h.1⟩ : (caught s l u A U x∧caught s l u A U (x-step i)))]
    rename_i h; rw [if_neg (fun g=>h ⟨g.2,g.1⟩)]; unfold RevB Step.used; simp only [↓reduceIte,Bool.true_xor,Bool.false_xor]; rw [flip_spin]
include W B
lemma turns(h:Rides j x p A A')(v:edge_h j x p R R'): make s l u T F A R (O U)= O (make s l u T F A' R' U) :=by
 funext ⟨i,d⟩; rw [opt_link d j x p (make s l u T F A' R' U),fare,make]; let k:=(posDir d).rotate j
 dsimp only; have ht:G (i+step d)=G i+k.vec:= opt_next (posDir d) j x i
 rw [caught_spin p U h, caught_spin p U h,canopy p U W B h,canopy p U W B h,ht]; change (if (_∧_) then _ else decideG _ _ _)= ακ (if caught s l u A' U (G i)∧ caught s l u A' U (G i+k.vec) then _ else decideG (ticket R' k (G i)) _ _); split; · exact opt_link d ..
 have hs:sendEdge j x (i,d)= k.used (G i):=by rw [facet_eq]; rfl
 rw [v (i,d), hs]; unfold ticket; rw [RevB,RevB,show k.neg=j.flip d from Bool.false_xor _, Bool.false_xor,decide_spin] -- projections issue
end Score
end YM.CF.BProof.Mesh.Shore
