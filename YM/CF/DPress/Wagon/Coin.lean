import YM.CF.DPress.Wagon.Reach
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Coin
-- normalization algebra reflected interval Bound.Cash.Earn, exponent choices when using it.
abbrev σ(n:Side) := (More n).val
def exp₄ (n:Side)(x:ℝ):= Real.exp (x* (σ n:ℝ)^4)
def exp₃ (n:Side)(x:ℝ):= Real.exp (x* (σ n:ℝ)^3)
lemma oneP {u:ℝ}(p:0≤u)(n:Side):1 ≤ exp₃ n u:= Real.one_le_exp (mul_nonneg p (by positivity))
lemma exp_max (u:ℝ) (n:Side): exp₃ n u ^ (σ n)= exp₄ n u:=by rw [exp₃,←Real.exp_nat_mul,exp₄]; congr 1; ring
lemma powC(x y:ℝ)(p:x<y)(n:Side):exp₄ n x<exp₄ n y:=Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right p (by have h:0<(σ n:ℝ):=(by unfold σ; positivity); positivity)) -- tune newline
variable {S:BandWidth} {r k:ℕ}{A:Bands (More n) S} (p:Buses.Sign S L k r) {H V:ℝ}
open Race Buses
abbrev tick(L:Side)(n:Side)(x:ℝ):= Real.exp (x*(2*(L.val:ℝ)) * (σ n:ℝ)^3)
lemma tally (X:Race n L)(x:ℝ): tick L n x ^ X.η=exp₄ n x:=by
 have ht:2*(L.val:ℝ) * X.η = (σ n:ℝ):=by rw [mul_assoc,show (L.val:ℝ)*X.η=n.val from (Nat.cast_mul ..).symm.trans (congrArg Nat.cast X.height)]; change _= (↑(n.val*2):ℝ); push_cast; ring
 unfold tick exp₄; rw [← Real.exp_nat_mul]; congr 1; rw [pow_succ' (n:=3)]; conv_rhs=> rw (occs := [1]) [←ht];
 ring
abbrev stake(k:ℕ)(u v:ℝ):= (k+1:ℝ)*(u+1)+ (k:ℝ)*(v+1)
include p in
lemma mix (A:Bands (More n) S) : (tick L n (-stake k H V)* (tick L n (V+1))^k)^A.Q.val=exp₄ n (-(H+1)):=by
 rw [← tally (mint A p) (-(H+1))]; let K:= Wall.len L; change _= _^(A.Q.val*(k+1)); unfold tick; rw [←Real.exp_nat_mul,←Real.exp_add,←Real.exp_nat_mul,←Real.exp_nat_mul]; congr 1; unfold stake; push_cast; ring
variable {b:ℕ}
lemma portionC (T:Race n L){v:ℕ}(p: b*v=T.η)(h:1≤ v): b ≤ σ n:= by
 have ht:b ≤ b*v:= Nat.le_mul_of_pos_right b (by omega); rw [p] at ht; let H:=T.η; have h:H≤ n.val:=by rw [← T.height]; exact Nat.le_mul_of_pos_left _ L.property
 exact ht.trans (h.trans (Nat.le_mul_of_pos_right n.val (by decide : 0 < 2))) -- tune semicolon
abbrev Pack {n:Side}(H:ℝ)(F:Fixed.Test n):Prop:=Measurable F∧ ∀ i, ‖F i‖≤ exp₄ n H
lemma pack_P (A:Bands (More n) S) (p':0 ≤ H)(p:Buses.Sign S L k r)(s:ℕ) (h:s*k=(mint A p).η){a:ℤ}{b:Bool}{F:Fixed.Test n}(u:Race.Credit (sharp A p (oneP p' n)).full a b (List.replicate s true) F) : Pack H F:=by
 have he:s≤ σ n:=portionC (mint A p) h (Buses.signk p); obtain k:= u.tag; have ht:(List.replicate s true).length=s:= List.length_replicate; refine ⟨k.borel,fun i=>(k.cost i).trans ?_⟩; change (exp₃ n H)^_≤ _; rw [ht,←exp_max]; gcongr; exact oneP p' n
lemma pack_t (A:Bands (More n) S) (p':0 ≤ H)(p:Buses.Sign S L k r) {X:A.Index→Fixed.Test n}(v:∀ i,IsMark (A.band i) (X i) (exp₃ n H)): Pack H (((bill A A.Q.val).map X).prod):=by
 obtain ⟨c,Hx,U⟩:= shout A p (oneP p' n) v A.Q.val le_rfl; let S:= sharp A p (oneP p' n); have he:A.Q.val ≤ σ n:=portionC (mint A p) (Buses.board_v A p (oneP p' n)) (S.stripe (sit_T A p (oneP p' n))).p; refine ⟨U.tag.borel,fun i=> (U.tag.cost i).trans ?_⟩; rw [Hx]; change ((exp₃ n H)^1)^_≤_; rw [pow_one,←exp_max]; gcongr; exact oneP p' n
lemma pack_one (n:Side)(p:0 ≤ H) : Pack H (1:Fixed.Test n) :=⟨measurable_const,fun i=>by rw [Pi.one_apply,norm_one,←exp_max]; exact one_le_pow₀ (oneP p n)⟩ -- tune Bool
end Coin
end YM.CF.DPress.Wagon
