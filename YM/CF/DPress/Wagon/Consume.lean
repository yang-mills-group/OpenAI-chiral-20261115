import YM.CF.DPress.Wagon.Coin
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
open Race Buses
variable {H V:ℝ}{r k i:ℕ}{S:BandWidth}(A:Bands (More n) S) (p:Buses.Sign S L k r)(v:0≤H)
-- The UV error line is at fixed s. Assemble cost variant with slack and *no* limiting assumption on vac itself.
def Bounty (H:ℝ)(f:Fixed.Test n→ℝ):Prop := ∃ U: A.Index→ Fixed.Test n,(∀ i,IsMark (A.band i) (U i) (exp₃ n H)) ∧ exp₄ n (-H) ≤ f (((bill A A.Q.val).map U).prod)
def Cr (n:Side) (k:ℕ)(H V:ℝ) := min (exp₄ n (V+1)-exp₄ n V) (min (exp₄ n (-H)-exp₄ n (-(H+1))) (exp₄ n (-stake k H V)-exp₄ n (-(stake k H V+1)))) -- tune succ
lemma pos_C (n:Side)(k:ℕ)(H V:ℝ): 0 < Cr n k H V:= lt_min (sub_pos.mpr (powC _ _ (by linarith) _)) (lt_min (sub_pos.mpr (powC _ _ (by linarith) _)) (sub_pos.mpr (powC _ _ (by linarith) _))) -- tune ∀
include v p
theorem Hearth {f g:Fixed.Test n→ℝ}(h: (mint A p).Bound g) (G:2^i=k)(p':2^(i+1)∣A.Q.val)(hg:∀ T:Fixed.Test n, Pack H T→ f T≤exp₄ n V)(hv:∀ T:Fixed.Test n,Pack H T→ |f T-g T| < Cr n k H V) (F:Bounty A H f): exp₄ n (-(stake k H V+1))< f 1:=by
 let S:= mint A p; let Z:=sharp A p (oneP v n); let P:= tick L n; let A0:= stake k H V; let R:=exp₄ n; let C:= Cr n k H V; by_contra! hx; have hp:g 1 ≤ P (-A0)^ S.η:=by
    rw [show P (-A0)^S.η=R (-A0) from tally S _]; have he:= hv 1 (pack_one n v); have hz: C ≤ R (-A0)-R (-(A0+1)):= (min_le_right ..).trans (min_le_right ..); change R (-(A0+1)) ≥ f 1 at hx; have hw:-(R (-A0)-R (-(A0+1))) ≤ f 1-g 1:= by linarith [(abs_lt.mp he).1]
    linarith
 have ht: Z.allE (P (V+1)) g:=by
    intro k t a b F p'; have u:= pack_P A v p _ t p'; have hv' := (abs_lt.mp (hv _ u)).1; have hq:= hg _ u; have hp:C ≤ R (V+1)-R V:=min_le_left ..; rw [show P (V+1)^S.η= _ from tally S _]; -- maybe binder reducible
    change g _ ≤ R (V+1); linarith
 obtain ⟨s,f',v'⟩:=F; let F0:= ((bill A A.Q.val).map s).prod; let t:= pack_t A v p f'; have he: g F0 ≤ R (-(H+1)):= (peak A p (oneP v n) f' h G p' (Real.exp_pos _) (Real.exp_pos _) hp ht).trans_eq (mix p A); have hu:C≤ R (-H)-R (-(H+1)):= (min_le_right ..).trans (min_le_left ..); have hz:f F0-g F0<C:= (abs_lt.mp (hv F0 t)).2; change _ ≤ f F0 at v'; linarith
end Coin
end YM.CF.DPress.Wagon
#print axioms YM.CF.DPress.Wagon.Coin.Hearth
