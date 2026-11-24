import YM.CF.Buffered.Oblique
/-! Spartan band census reduces comparison rate from volume-exponential to
 area-times-polylog. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Crust.Grid
open Function Filter Finset Lattice Wilson RG PathData Work.F03
open Cube Region Roost Rush
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators Topology
variable {G:Gauge}{N P D:Side}{a b:ℝ}{s:ℕ}
def gutter (P:Side)(s:ℕ) : Finset (Per P) := univ.filter fun x=> x.val < s ∨ P.val≤x.val+s
lemma gutter_count (P:Side)(s:ℕ) : (gutter P s).card ≤ 2*s := by
 let f:ℕ→ Per P:=fun i=>i; let T:=range s; let Y:= T.image f; let Z:=T.image fun i=> -(f i+1); have he : (gutter P s)⊆ Y∪Z:=by
    intro i h; obtain p|p:= (mem_filter.mp h).2; exact mem_union_left _ (mem_image.mpr ⟨i.val, mem_range.mpr p,ZMod.natCast_zmod_val _⟩) -- tune
    refine mem_union_right _ (mem_image.mpr ⟨P.val-(i.val+1), mem_range.mpr (by have ht:= i.val_lt; omega),?_⟩)
    unfold f; rw [Nat.cast_sub (Nat.succ_le_of_lt i.val_lt),ZMod.natCast_self]; push_cast; rw [ZMod.natCast_zmod_val]; abel
 refine le_trans (card_le_card he) ((card_union_le ..).trans ?_); have ht:Y.card≤ s:=card_image_le.trans_eq (card_range _); have hv: Z.card≤ s:=card_image_le.trans_eq (card_range _); omega
lemma strip_count (P:Side)(s:ℕ) : (stripP P s).card≤ 4*(4*(2*s*P.val^3)):=by
 let f(u:Axis)(t:Axis) := if u=t then gutter P s else univ; let Z(u):= Fintype.piFinset (f u)
 let X:= univ.biUnion Z; let A:=X ×ˢ (univ:Finset Axis)
 refine le_trans (card_le_card (show stripP P s ⊆ A from ?_)) ?_; ·
    intro u p; by_contra h; apply strip_iff s u |>.2 ?_ p; intro i
    have hp:u.1∉ Z i:=fun v=> h (mem_product.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,v⟩,mem_univ _⟩)
    let x:=u.1
    have he:x i ∉ gutter P s:=fun v=> hp (Fintype.mem_piFinset.mpr fun j=> by
       change u.1 j ∈ f i j
       by_cases h:i=j; · rw [←h]; unfold f; rw [if_pos rfl]; exact v
       unfold f; rw [if_neg h]; exact mem_univ _)
    simp only [gutter,mem_filter,mem_univ,true_and,not_or] at he; change ((s:ℤ)≤ ↑(x i).val) ∧ ↑(x i).val+(s:ℤ)<P.val; omega
 have hp(i): (Z i).card = (gutter P s).card*P.val^3:=by
    unfold Z; rw [Fintype.card_piFinset,←mul_prod_erase univ _ (mem_univ i)]; simp_rw [f,if_true]; congr 1 -- tune simp if_true
    -- product constant; simplify
    rw [prod_congr rfl (g:=fun _=>P.val) (fun j h=> by simp only [if_neg (Ne.symm (mem_erase.mp h).1),card_univ]; exact ZMod.card _)]
    simp
 rw [show A.card=_ from card_product ..,card_univ, show Fintype.card Axis=4 from Fintype.card_fin _,mul_comm]
 refine Nat.mul_le_mul_left 4 ((card_biUnion_le).trans ?_); simp_rw [hp]; simp only [sum_const,card_univ,Axis,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]; exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ (gutter_count ..))
end YM.CF.Buffered.Crust.Grid
