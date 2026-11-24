import YM.CF.BProof.Grid.System

/-! Dyadic split. Evaluate equal corner average indexed with the unused bits
of a boundary cell duplicated. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Set Function Lattice Entity Finset
open scoped Classical
variable {n : ℕ} {c s : Side} (g : Ratio c s)

abbrev Dice (n : ℕ) := Fin n→ Bool
def eighth (x:Cubic n s)(b : Dice n) : Cubic n c := fun i=> if (here g x i).val=0 ∨ b i=false then elder g x i else elder g x i+1

def node8 (x:Cubic n s)(b : Dice n) : Cubic n s := grow g (eighth g x b)

variable (p:Entity n c)
private lemma elder_step (x:Cubic n s) {i:Fin n} (h:p.coord g x i<g.count.val) : elder g x i=p.home i:= (block_eq g (x i) _).mpr ((mem_tile ..).mpr h)
private lemma lastB (x:Cubic n s){i:Fin n}(h:p.coord g x i=g.count.val): x i=base g (p.home i+1):=by rw [base_add,base_one]; exact (show p.first g i+g.count.val=x i from h ▸ add_along (p.first g i) (x i)).symm
lemma cornersB (x:Cubic n s) (b:Dice n)(hx:p.Mem g x)(i:Fin n) :
    eighth g x b i= if p.coord g x i=0 ∨ p.coord g x i < g.count.val ∧ b i=false then p.home i else p.home i+1 := by
 let a:=p.coord g x i; have ht:a≤g.count.val:=(hx i).trans (p.width g i); have hz:0<g.count.val:=g.count.property
 rcases ht.lt_or_eq with h|h
 · have he : (here g x i).val=a:=by
     have hv:= stamp_native g 0 (p.home i) h; rw [native, origin,zero_add, show base g _+(a:Per s)=x i from add_along ..] at hv; simpa only [stamp,off,sub_zero,here] using hv
   unfold eighth; change _ = if a=0 ∨ a<g.count.val ∧ _ then _ else _; simp only [elder_step g p x h,he,h,true_and]
 have he:= lastB g p x h
 unfold eighth elder here; simp only [he]; have hh:= hu_aux g (p.home i+1)
 rw [hh.1,hh.2, if_pos (Or.inl rfl), if_neg]; change ¬(a=0∨a<g.count.val ∧ _); omega
 where
 hu_aux (g : Ratio c s)(i : Per c) : (part g (base g i)).val=0 ∧ block g (base g i)=i:= by
   have hz:0<g.count.val:=g.count.property; refine ⟨?_,?_⟩; simpa [stamp,native_zero,origin,off] using stamp_native g 0 i hz; simpa only [Nat.cast_zero,add_zero] using block_add g i hz

abbrev next8 (a r:ℕ)(b : Bool) : ℕ:= if a=0∨ a<r∧ b=false then 0 else r
lemma node_spec (x:Cubic n s)(b:Dice n)(hx:p.Mem g x) : node8 g x b = p.put g (fun i=>next8 (p.coord g x i) g.count.val (b i)) := by
 ext i; unfold node8 grow put Entity.first; rw [cornersB g p x b hx i]; unfold next8; split_ifs <;> simp [grow] <;> grind
lemma placed (hc:4≤c.val)(x:Cubic n s)(b:Dice n)(hx:p.Mem g x) : p.Mem g (node8 g x b):=by
 rw [node_spec g p x b hx]; apply p.mem_put g hc; intro i; by_cases h:i∈p.axes; unfold Entity.len; rw [if_pos h]; unfold next8; dsimp only; split_ifs <;> omega; have hp : p.len g i=0:=if_neg h; have hh : p.coord g x i=0:= Nat.eq_zero_of_le_zero ((hx i).trans_eq hp); simp [next8,hh]

-- at a fine edge, for comparison use full cube on that edge. One of
-- the two has coord i=1 and the other pinned at 0 or 2. The pairing
-- matches for precisely one of the values of b at i.
lemma clicked (hc:4 ≤ c.val) (hu : g.count.val=2) (x:Cubic n s)(i:Fin n) (hx:p.Mem g x)(hv:p.Mem g (slide x i)) :
    ∃ b : Bool, ∀ a : Dice n,
      if a i=b then eighth g x a=eighth g (slide x i) a else eighth g (slide x i) a = slide (eighth g x a) i := by
 let l:=slide x i; let K:=p.coord g x
 have hh := (p.stepMem g i hc hx).1 hv; have hk : K i ≤ 1:=by have hp:=p.width g i; change _<_ at hh; unfold K; omega
 have hg (a : Dice n)(j : Fin n)(h:j≠i): eighth g l a j=eighth g x a j:=by rw [cornersB g p _ _ hv,cornersB g p _ _ hx,p.coord_step g x hx i hc,update_of_ne h]
 have he(a : Dice n):eighth g l a i= if K i+1<2 ∧ a i=false then p.home i else p.home i+1:=by rw [cornersB g p _ _ hv,p.coord_step g x hx i hc]; simp [K,hu]
 refine ⟨decide (K i=1),fun a=>?_⟩; change ite _ (eighth g x a=eighth g l a) (eighth g l a= _)
 split_ifs with h
 · ext j; by_cases v:j=i; subst j; rw [cornersB g p x a hx i,he,hu,h]; change ite (K i=0∨K i<2 ∧ _) _ _ = _; grind; exact (hg a j v).symm
 ext j; by_cases v:j=i; subst j; rw [slide_i,he,cornersB g p x a hx i,hu]; change _ = ite (K i=0∨K i<2 ∧ _) _ _ + 1; grind
 rw [slide_at _ v,hg a j v]
end YM.CF.BProof.Grid
