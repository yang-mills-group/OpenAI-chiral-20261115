import YM.CF.BProof.Tape.Pear
import YM.CF.BProof.Stint.Ticker

/-! Bias accounting route. In particular no H contributions at all in
`purseT` matrix trace-labelling; and choose gauge-invariant support terms of losses
in the same field arguments throughout homogeneous and dynamic references. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tape
open Function Filter Fock Finset Branch Stint Align Wick Hearth Spin Tenant Lat Lattice Tulip Cube Fig Push.AbsoluteSums
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P: Ready j a b l r}{F:Core j a b l r N}(h:Honor P F δ)(x:Loft F δ c v η)
def bias (x: Loft F δ c v η)(o:Site (More N)):ℝ:= (peak (iron N 0 0).st o (billR x)).re
lemma peak_same {D:Type}(b:Feet N D)(o:Site (More N))(A:Op (Single N)): peak b.st o A= peak (iron N 0 0).st o A:=by unfold peak strip board; rw [b.index]; rfl
abbrev offProfit(x:Loft F δ c v η) := widthP (piF x.val.1) (view x (false,false) 1)
lemma levy (o:Site (More N)) : let T:= (peak (iron N 0 0).st o (offProfit x)).re; bias x o ≤ -(1/4:ℝ)*T ∧ 0≤T:= by
 intro T; let b:=(iron N 0 0).st; let A:= offProfit x; let Y:= board b {o}; let t:=x.val.1; let S:= x.val.2; let P:= piF t
 have hu:Shelf _ _ _:= (show Ride .. from x.property).pores 1 walk1; have he: ‖A‖<1:= (widthN' _ _ _ t.property (pairBy ..) hu).trans_lt hu.small; have hy:0 ≤ A:= width_pos ..
 constructor
 · change (peak b o ((1/4:ℂ) • pencil (-A))).re ≤ -_* _; rw [peak_eq, show T=∑ i∈Y,(A i i).re from (by unfold T; rw [peak_eq,Complex.re_sum])]; simp_rw [Complex.re_sum, Matrix.smul_apply]; rw [mul_sum]; apply sum_le_sum; intro i _; have ht:= diagonal_le _ _ (negPastel he hy) i; norm_num at ht ⊢; linarith only [ht]
 -- tune
 unfold T; rw [peak_eq,Complex.re_sum]; apply sum_nonneg; intro i _; exact diagonal_le _ _ hy i
lemma bias_zero (o:Site (More N))(e: offProfit x=0):bias x o=0:=by unfold bias billR periodQ; rw [show widthP (piF x.val.1) _= _ from e,neg_zero,pastel_zero,smul_zero]; simp [peak] -- tune
lemma scroll {p:Pay}(w:Tickets p P δ c v η F h.1): let b:=(Tape.kiln h.1 c v η).st; ∃ (E: Ticker b billR)(Q:Ticker (h.1.beam c).st purseT)(V:Ticker b labelR), let C:= fun (F:Site (More N) × Seal (Site (More N))→ℝ)=> Moment.Toll Prod.snd F (p.rate/2) (vaultPay p quota); C E.pay∧ C Q.pay∧ C V.pay := by
 intro b; obtain ⟨E,hE⟩:= tickable Spin.quota_p.le (Tape.kiln h.1 c v η).cap w.2.1; obtain ⟨Q,hQ⟩:= tickable Spin.quota_p.le (h.1.beam c).cap w.1; obtain ⟨S,hS⟩:=tickable Spin.quota_p.le (Tape.kiln h.1 c v η).cap w.2.2.1; exact ⟨E,Q,S,hE,hQ,hS⟩
end YM.CF.BProof.Tape
