import SatinThinOort
set_option autoImplicit false
noncomputable section
namespace YM.Pressure.Worth.Pays
open Function Filter Finset Lattice CF.BProof
open scoped Topology
abbrev terrace (x:ℝ):Side:=⟨Nat.ceil (widthC x),Nat.ceil_pos.mpr (coin_pos ..)⟩
lemma terrace_size : Pays r_width 0 0 fun x=>((terrace x).val:ℝ):=by
 apply by_floor (C:=2); filter_upwards [coin_budget (d:=r_width) (b:=0) (c:=0) (e:=0) (f:=0) (Or.inl (by norm_num [r_width] : (0:ℝ) < r_width)) 1 1 zero_lt_one] with x hx
 have hp:1 ≤ widthC x:=by simpa only [coin_zero,one_mul] using hx.le; -- ;
 have ht:=Nat.ceil_lt_add_one (coin_pos x r_width 0 0|>.le); rw [abs_of_nonneg (Nat.cast_nonneg _)]; unfold terrace widthC; dsimp; unfold widthC at hp; linarith only [hp,ht.le] -- tune
lemma terrace_mm (x:ℝ) : widthC x≤ ((terrace x).val:ℝ):= Nat.le_ceil _
lemma terrace_inv : Pays (-r_width) 0 0 fun x=>(((terrace x).val:ℝ))⁻¹:=by
 apply by_floor (C:=1); apply Eventually.of_forall; intro x
 have hp:0< (↑(terrace x).val:ℝ):= Nat.cast_pos.mpr (terrace x).property; rw [abs_of_nonneg (inv_pos.mpr hp|>.le),one_mul]; refine (inv_anti₀ (coin_pos x r_width 0 0) (terrace_mm x)).trans_eq ?_; rw [coin_inv]; simp
lemma property_plus : Pays 0 0 2 (fun x=> (radiusB x:ℝ)+1) := plus rising (merit (constant 1) (by refine Or.inr (Or.inr ⟨rfl,rfl,?_⟩); norm_num))
end YM.Pressure.Worth.Pays
