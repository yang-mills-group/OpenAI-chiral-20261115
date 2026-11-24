import YM.CF.BProof.Grid.Dyad
import YM.CF.BProof.Grid.Patch

/-! On corner meshes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Function Lattice Entity
variable {n : ℕ}{s c : Side}(g:Ratio c s)(p:Entity n c)

def digit (s:Side) : Ratio s s:=⟨1,by simp⟩
@[simp] lemma digit_base {x : Per s} : base (digit s) x=x := by nth_rw 1 [← ZMod.natCast_zmod_val x]; rw [base_nat]; simp [digit]
@[simp] lemma digit_grow (x:Cubic n s) : grow (digit s) x=x := by ext; simp [grow]
@[simp] lemma digit_count : (digit s).count.val=1:=rfl
lemma dimension (x:Cubic n c) : p.Mem g (grow g x) ↔ p.Mem (digit c) x := by
 unfold Entity.Mem coord; apply forall_congr'; intro i; rw [Entity.first,Entity.first,digit_grow]; change along (base g _) (base g (x i)) ≤ _ ↔ _; rw [base_distance]; unfold Entity.len; split
 next _=> rw [digit_count]; nth_rw 2 [← mul_one g.count.val]; -- tune
          exact Nat.mul_le_mul_left_iff g.count.property
 next _=> simp [show 0<g.count.val from g.count.property,Nat.pos_iff_ne_zero] -- tune
lemma facing (x:Cubic n c)(b:Dice n): eighth g (grow g x) b=x:=by
 ext i; unfold eighth; have hz: (here g (grow g x) i).val=0:=by change (part g (base g _)).val=0; have h:= stamp_native g 0 (x i) (ha:= g.count.property); simpa [stamp,native_zero,origin,off] using h
 rw [hz,if_pos (Or.inl rfl),elder_grow]

-- child step embedding price both edges in cell. special step =2.
lemma midpoint (x:Cubic n c)(i:Fin n)(hc:4≤c.val)(h:g.count.val=2) (hp:p.Mem (digit c) x)(hv:p.Mem (digit c) (slide x i)) : p.Mem g (slide (grow g x) i):=by
 apply (p.stepMem g i hc ((dimension ..).mpr hp)).2
 have hx: p.coord (digit c) x i < p.len (digit c) i:= (p.stepMem (digit c) i hc hp).1 hv
 by_cases v:i∈p.axes
 · simp only [len, v,↓reduceIte] at hx ⊢; rw [digit_count] at hx
   unfold Entity.coord first grow; rw [base_distance]; have hv : along (p.home i) (x i)=0:= by unfold Entity.coord first at hx; rw [digit_grow] at hx; exact Nat.lt_one_iff.mp hx
   rw [hv]; simp [h]
 simp [len,v] at hx
end YM.CF.BProof.Grid
