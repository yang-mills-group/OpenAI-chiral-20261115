import YM.CF.BProof.Shore.Warm
/-! Symmetry -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Metric Finset Lattice Wilson Nest Stave Gallery
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
open Wool
variable {T:Tray (Floor q) ε}{F:Drum (rollup q T) (Floor q)} {A A':Score n q}
structure Rides (j:Signed)(x:Site n)(p:Bool) (A B:Score n q):Prop where
 spin0: Equates (facet j x) A.cur B.cur
 spin1: Equates (facet j x) A.fine B.fine
 order(i): B.orderC (facet j x i)=orderEquiv j (A.orderC i)
 turn(i): A.fire i=p.xor (B.fire (facet j x i))
variable {j:Signed}{x:Site n}(p:Bool)(U:Config SU.group n) (W:Writ q T s l u a b δ d θ F) (B:Seal A s l b a)
local notation "hΨ"=>facet j x
local notation "Ω"=>A.cur.native A.orderC
local notation "Ω'"=>A'.cur.native A'.orderC
local notation "Ζ"=>Opts j x p U
lemma caught_spin (h:Rides j x p A A')(i:Sκ): caught s l u A Ζ i↔ caught s l u A' U (hΨ i):=by
 constructor; intro z k t; obtain ⟨k,rfl⟩:=(hΨ).surjective k; exact opt_p ..|>.1 (z k ((spun _ h.spin1 ..).2 t)); intro z k t; exact opt_p ..|>.2 (z _ ((spun _ h.spin1 ..).1 t)) -- tune sound equiv inferred
include B
lemma spinCar(h:Rides j x p A A')(i:Sκ): Ω Ζ i= dye p (Ω' U (hΨ i)):= n_rev B.ch _ _ B.small h.spin0 h.order i
lemma keys(h:Rides j x p A A')(i:Sκ): Key T A Ζ i=(if p then (T.house (Fin q)).μ else Equiv.refl _) (Key T A' U (hΨ i)):=by
 unfold Key; rw [spinCar p U B h i,h.spin1.1 i,h.turn]; cases p; · rw [Bool.false_xor]; rfl
 rw [Bool.true_xor]; exact T.marks ..
def rotate {q:ℕ}{ε:ℝ}(T:Tray (Floor q) ε) (p:Bool): Equiv.Perm (rollup q T) := if p then (T.house (Fin q)).μ else Equiv.refl _
lemma spinTeam(h:Rides j x p A A')(i:Sκ): tagger s l u T A Ζ i=octa (rotate T p) (tagger s l u T A' U (hΨ i)):=by
 let b:=hΨ; let k:=rotate T p; ext x'; unfold tagger bale octa; dsimp only; nth_rw 2 [← Equiv.sum_comp b]; apply sum_congr rfl; intro j' _
 have l : sound s l u Ζ j'↔ sound s l u U (b j'):= opt_p (r:=Radius s l) j x p U j'; simp only [l,show Key T A Ζ j'=(rotate T p) (Key T A' U (b j')) from keys p U B h j',Equiv.apply_eq_iff_eq_symm_apply,h.spin1.2 i j']; unfold b; congr!
include W
lemma canopy(h:Rides j x p A A')(i:Sκ): opened s l u T F A Ζ i= dye p (opened s l u T F A' U (hΨ i)):=by
 unfold opened; rw [←caught_spin p U h]; split; rename_i z; · rw [spinCar p U B h]; cases p; rfl; exact (blink_lower ..).symm
 rename_i z; rw [spinTeam p U B h]; cases p; rfl; exact transitY W.book _
end Score
end YM.CF.BProof.Mesh.Shore
