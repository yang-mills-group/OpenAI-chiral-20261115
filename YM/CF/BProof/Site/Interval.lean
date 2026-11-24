import YM.CF.BProof.Strip

/- single-axis distance and interval padding, price distances (≤ b). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Circle
open Function Lattice Finset Cube
open scoped Topology BigOperators Classical
variable {s:Side}(a x:Per s)(l:ℕ) (r:ℕ)
abbrev δ (x y:Per s):= delta1 s x y
-- trichotomy distance
lemma lag (y:Per s) (h:x≠y): along x y+along y x =s.val:=by
 unfold along; rw [← neg_sub (y) x,ZMod.neg_val,if_neg (show y-x≠0 from sub_ne_zero.mpr h.symm)]; have ht:=ZMod.val_lt (y-x); omega -- tune `neg_val`
lemma δle (y:Per s): δ x y≤ r ↔ along x y≤r ∨ along y x≤r:=by
 by_cases hx:x=y; subst y; simp [δ,d_id]; rw [δ,d_sym,delta_eq]; have hg:= lag x y hx; omega
lemma triangle (x y z:Per s): along x z≤along x y+along y z:=by
 by_cases h:along x y+along y z<s.val
 · refine le_of_eq ?_; convert along_add x h using 2; rw [Nat.cast_add,← add_assoc,add_along,add_along]
 have hp:= along_lt x z; omega
lemma deposit (y:Per s)(h: along a x+along x y < s.val) : along a y=along a x+along x y:=by
 convert along_add a h using 2; rw [Nat.cast_add,← add_assoc,add_along,add_along]
lemma distance (y:Per s)(h:along a x≤along a y): along a y=along a x+along x y:=by
 have he: along x y=along a y-along a x:=by
   convert offset_dist a h (show along a y-along a x<s.val from Nat.lt_of_le_of_lt (Nat.sub_le ..) (along_lt ..)) using 2<;> rw [add_along]
 omega
-- padding by r both sides
abbrev before : Per s:= a-r
abbrev padded := along (before a r) x ≤ l+2*r
lemma padL (d:ℕ): (a-(r:Per s))+(r+d :ℕ)=a+d:=by push_cast; abel
lemma pad_distance (h:along a x+r<s.val): along (before a r) x=along a x+r:=by
 rw [← along_add (before a r) h,Nat.cast_add]; rw [add_comm (↑(along a x):Per s) (r:Per s),← add_assoc, before,sub_add_cancel,add_along]
lemma pad_mem (y:Per s)(h:along a x ≤ l)(p:δ x y≤ r)(hv:l+2*r<s.val) : padded a y l r :=by
 rcases (δle x r y).1 p with hh|hh
 · unfold padded; apply (triangle _ x _).trans; rw [pad_distance _ _ _ (by omega)]; omega
 have hu: along (before a r) x=along a x+r:=pad_distance _ _ _ (by omega)
 -- y preceding x. if wraps crossing padded start, would require r> distance to it.
 unfold padded; by_contra q
 have hg:= distance (before a r) x y (by omega); by_cases he:x=y; subst y; omega
 have hk:=lag x y he; have := along_lt (before a r) y; omega
lemma pad_wing (g:padded a x l r)(hv:l+2*r<s.val): along a x≤l ∨ along x a≤r ∨ along (a+(l:Per s)) x≤r:=by
 unfold padded at g; by_cases h:along (before a r) x≤r
 · right; left; have he:=pad_distance a a r (by simp; omega); rw [along_self,zero_add] at he; have hp:=distance (before a r) x a (h.trans_eq he.symm); omega
 have he:=pad_distance a a r (by simp; omega); rw [along_self,zero_add] at he
 have hp:=distance (before a r) a x (by omega); by_cases k:along a x≤l; exact Or.inl k
 right; right; have hu:= along_add a (show l<s.val from by omega); have hg:=distance a (a+l) x (by omega); omega
lemma dwings : before a r+r=a:=sub_add_cancel ..
lemma pad_iff (hv:l+2*r<s.val): padded a x l r ↔ ∃ y, along a y≤l∧ δ y x≤ r:=by
 refine ⟨fun h=>?_,fun ⟨y,h,p⟩=> pad_mem a y l r _ h p hv⟩; rcases pad_wing a x l r h hv with h|h|h; exact ⟨x,h,by simp [δ,d_id]⟩; exact ⟨a,by simp,(δle a r x).2 (Or.inr h)⟩; exact ⟨a+l,(along_add a (by omega)).le,(δle _ r x).2 (Or.inl h)⟩
/-- Deep interior of any short strip. -/
lemma deep (h:r≤along a x)(v:along a x+r≤l)(he:l+r<s.val)(y:Per s)(p:δ x y≤r): along a y≤l:=by
 rcases (δle x r y).1 p with h|hp
 · exact (triangle a x y).trans (by omega)
 by_contra u; have hv : along a x ≤ along a y:=(by omega); by_cases hs:x=y; subst y; omega
 have hg:=distance a x y hv; have hu:=lag x y hs; have := along_lt a y; omega
end YM.CF.BProof.Circle
