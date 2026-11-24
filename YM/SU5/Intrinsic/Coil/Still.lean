import YM.SU5.Intrinsic.Coil.Solos
import YM.SU5.Intrinsic.Coil.Carbon

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Coil.Chart.Stoke
open Function Lattice Finset Filter Stilo Palot RG Scree Skye Fock Tulip Sour
open Cube Pastry Vow Rue Stax Sault
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {I:Type}[DecidableEq I][Fintype I]{n:Side} {F:ForceBudget n}{P:BudgetPoint} {H:ℝ} {δ:ℕ}
variable {b:Force n→ℝ}{V:I→ Firing n}{a:I→ℝ}{B:Chart I (Seat n)}
variable (C:B.Stoke δ P H V a) (T:Blizzard F P H δ b)(L:Finset (I⊕ Force n))(S:Aura n)(D:Support (More n)) (l:List I)
open Push.AbsoluteSums Push.AbsoluteSums.Trees
lemma glint_one {vS:Finset (Duo (More n))}(h:vS.toRight=∅):beatB vS=weighH vS.toLeft:=by
 -- sup bypass cast between Seats
 generalize he:vS.toLeft=P
 have hh:= joinP vS; rw [he,h] at hh; subst vS
 unfold beatB rhythm weighH; apply le_antisymm
 · apply Finset.sup_le; intro i h; cases i with
   | inl i=> exact Finset.le_sup (f:=fun x:Aura n=>beamH x.val) (inl_mem_disjSum.mp h)
   | inr i=> exact False.elim (notMem_empty _ (inr_mem_disjSum.mp h))
 apply Finset.sup_le; intro i h; exact Finset.le_sup (b:=(Sum.inl i:Palot.Duo (More n))) (f:=fun i=>beamH ((stern ∘ dock) i)) (inl_mem_disjSum.mpr h)

lemma room_mask_zero (S:Aura n)(D:Support (More n))(K:Cusp n)(v:D⊆ S.val)(u:D.Nonempty):glowV K 0 S D= K S D:=by
 let J:Finset (Duo (More n)):= {Sum.inl S}; have ht(J:Aura n): ({Sum.inl J}:Finset (Duo (More n))).toRight=∅:=by ext; simp
 have hp: J.toLeft={S}:=Finset.ext (by simp [J]); have hs: beatB J=beamH S.val:=by rw [glint_one (ht S), hp]; simp [weighH]
 have hy:lumpD J D S:=by
    refine ⟨hs,?_⟩; unfold Palot.mine; rw [hp,ht S,hs,bay_beam]; obtain ⟨i,h⟩:=u
    refine ⟨fun x l y t z=> (z ((mem_singleton.mp l).trans (mem_singleton.mp t).symm)).elim,fun x g=>?_ ,fun _ p=> False.elim (notMem_empty _ p),by simpa [robe] using (inter_subset_right : D∩S.val⊆S.val)⟩
    rw [mem_singleton.mp g]; exact fun z=>Finset.disjoint_left.mp z (v h) h
 unfold glowV mintF; rw [if_pos v,sum_eq_single J,gear_v,if_pos hy, hp,ht S,prod_empty,prod_singleton,mul_one,inter_eq_left.mpr v]
 · intro i _ l; rw [Vow.gear_v]; split; next h=>
      by_cases a:i.toRight=∅; swap
      · obtain ⟨j,u⟩:= nonempty_iff_ne_empty.mpr a; rw [prod_eq_zero u (by rfl),mul_zero]
      have he: weighH i.toLeft=beamH S.val:=(glint_one a).symm.trans h.1; have ht':=emblem h.2.1; rw [he,singHs S] at ht'; exact False.elim (l (by nth_rw 1 [← joinP i]; rw [← ht',a]; ext x; cases x <;> simp [J]))
   next => rfl
 simp
lemma fog (p:BudgetPoint) : FeeD p (0:Pax n) = 0:=by
 funext s x; unfold FeeD spinD lasting zenS; split; swap; · rfl
 dsimp only; apply Eq.trans (tsum_congr (g:=fun _:ℕ=>(0:Cipher n)) ?_) tsum_zero; intro i; unfold funge; rw [Finset.sum_apply]; apply sum_eq_zero; intro j _; unfold Vow.sta; split; swap; · rfl
 unfold guava; rw [prod_eq_zero (mem_univ (none:Option (Fin i))) (by rfl), smul_zero]; rfl
lemma standBy (Q:Cusp n): budgetR (roomV P 0 Q 0) = budgetR Q:=by
 rw [roomV, fog P, show (boastV (0:Pax n) 0)=0 from ?_]; swap; · funext i D w; unfold boastV; change NormedSpace.exp (if D.Nonempty then (0:Cipher n) else -0)-1=0; rw [neg_zero, ite_self, NormedSpace.exp_zero, sub_self]
 funext i; unfold budgetR; rw [room_mask_zero _ _ Q i.property.2 i.property.1]

include T
lemma zeroLake:kiosk (C.issueK F l 0)=0:=by
 funext i; unfold kiosk; rw [baseK C T]; exact sum_eq_zero fun j p=> by have h:=j.property.1; rw [show j.val.2=∅ from (mem_filter.mp p).2.2] at h; exact False.elim (Finset.not_nonempty_empty h)
abbrev reanchor (F:ForceBudget n):Prop:=∃ K:Cusp n, F=budgetR K -- property we preserve
lemma zeroLedger (h:reanchor F):budgetR (C.issueK F l 0)=F:=by
 funext i; let X:=lordD i; let D:=extraD i; let V:=motV X D
 change bassH X • (C.issueK F l 0 X D)=F i; rw [baseK C T]; obtain ⟨u,v⟩:=h; have hi(j:Force n)(p:j∈V): F j=F i:=by obtain ⟨a,b⟩:= (mem_filter.mp p).2; rw [v,budgetR,a,b]; rfl
 rw [sum_congr rfl hi,sum_const,countV X (mem_filter.mpr ⟨mem_univ _,i.property⟩),← Nat.cast_smul_eq_nsmul ℝ]; exact (inv_smul_smul₀ (show (X.val.card:ℝ)≠0 from by exact_mod_cast (card_pos.mpr X.property).ne') _)
lemma birth_force (h:reanchor F): budgetR (roomV P (kiosk (C.issueK F l 0)) (C.issueK F l 0) 0)=F:= by rw [C.zeroLake T,standBy,C.zeroLedger T l h]
end YM.CF.Coil.Chart.Stoke
open YM.CF.Coil.Chart.Stoke
#print axioms fog
#print axioms birth_force
