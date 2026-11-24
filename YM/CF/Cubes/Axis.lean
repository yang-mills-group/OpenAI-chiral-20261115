import YM.CF.Cubes.Refine

/-! One-dimensional anchor geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat

abbrev CSide (m B : Side) := More m * B
abbrev Domain (m B : Side) := More (CSide m B)
abbrev GridN (m : Side) := More (More m)
def scaleR (m B : Side) : Ratio (GridN m) (Domain m B) := ⟨B, by simp [Domain,GridN,More,CSide,mul_right_comm]⟩
variable {m B N : Side}
lemma natM (m : Side) : (More m).val=m.val*2 := rfl
lemma wrap_here (n : Side) (x : Cover) (i : Axis) : wrap n x i = (x i:Per n) := rfl

def high (m : Side) (B : Side) (x : Per (GridN m)) : Per (Domain m B) := (scaleR m B).root (fun _=>x) 0
lemma high_here (m : Side) (B : Side) (x : Site (GridN m)) (i : Axis) : (scaleR m B).root x i = high m B (x i) := by
  unfold high Ratio.root Ratio.embed lift; rfl
lemma high_add (m : Side) (B : Side) (x y) : high m B (x+y)=high m B x+high m B y := by
  let a : Site (GridN m) := fun _ => x; let b : Site (GridN m) := fun _ => y
  change (scaleR m B).root (a+b) 0=_; rw [map_add]; rfl
lemma high_sub (m : Side) (B : Side) (x y) : high m B (x-y)=high m B x-high m B y := by
  let a : Site (GridN m) := fun _ => x; let b : Site (GridN m) := fun _ => y
  change (scaleR m B).root (a-b) 0=_; rw [map_sub]; rfl
lemma high_cast (m : Side) (B : Side) (j : ℤ) : high m B j=((B.val*j:ℤ):Per (Domain m B)) := by
  let x : Cover := fun _ => j
  change (scaleR m B).embed (wrap _ x) 0=_; rw [Ratio.embed_wrap,wrap_here]; congr 1
lemma high_inc (x) : high m B (x+1)=high m B x+B.val := by
  rw [high_add,← show high m B ((1:ℤ):Per (GridN m))=high m B 1 by norm_num,high_cast]; simp
lemma high_dec (x) : high m B (x-1)=high m B x-B.val := by
  rw [high_sub,← show high m B ((1:ℤ):Per (GridN m))=high m B 1 by norm_num,high_cast]; simp

def delta1 (N : Side) (x y : Per N) := (ZMod.valMinAbs (x-y)).natAbs
lemma d_one_triangle (x y z : Per N) : delta1 N x z ≤ delta1 N x y+delta1 N y z := by
  unfold delta1; rw [← sub_add_sub_cancel x y z]
  exact (ZMod.natAbs_valMinAbs_add_le ..).trans (Int.natAbs_add_le ..)
lemma d_sym (x y : Per N) : delta1 N y x=delta1 N x y := by unfold delta1; rw [← ZMod.natAbs_valMinAbs_neg,neg_sub]
lemma d_id (x : Per N) : delta1 N x x=0 := by simp [delta1]
lemma d_shift (x y z : Per N) : delta1 N (x+z) (y+z)=delta1 N x y := by simp [delta1]
lemma d_equal (x y : Per N) (g : delta1 N x y=0) : x=y := by
  apply sub_eq_zero.mp; rw [← ZMod.coe_valMinAbs (x-y),Int.natAbs_eq_zero.mp g]; simp
lemma d_unit (x y : Per N) (g : delta1 N x y=1) : x=y+1 ∨ x=y-1 := by
  let i := x-y; have he : i.valMinAbs.natAbs=1 := g
  have hi : x=y+((i.valMinAbs:ℤ):Per N) := by rw [ZMod.coe_valMinAbs]; unfold i; abel
  rcases (show i.valMinAbs=1 ∨ i.valMinAbs= -1 from by omega) with h|h <;> rw [h] at hi
  · left; simpa using hi
  right; simpa [sub_eq_add_neg] using hi
lemma d_high (x y) : delta1 (Domain m B) (high m B x) (high m B y)=B.val * delta1 (GridN m) x y := by
  rw [delta1,←high_sub]; unfold high
  change (lift ((scaleR m B).embed (fun _=>x-y)) 0).natAbs=_
  rw [Ratio.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul]; rfl

def OddAxis (m : Side) (x : Per (GridN m)) := ((assembly (More m)).residue (fun _=>x) 0) = 1
instance (x) : Decidable (OddAxis m x) := by unfold OddAxis; infer_instance
lemma oddAtAdd (x : Per (GridN m)) : OddAxis m (x+1) ↔ ¬ OddAxis m x := by
  unfold OddAxis; let f := assembly (More m); change f.residue _ _=1 ↔ _
  have he : f.residue (fun _ => x+1)= f.residue (fun _=>x) + 1 := by
    rw [show (fun _ : Axis => x+1)=(fun _:Axis=>x)+wrap _ 1 by funext i; simp [wrap_here],map_add,Ratio.residue_wrap]
    congr 1
  rw [he]; change let a : ZMod 2 := f.residue (fun _=>x) 0; a+1=1 ↔ a≠1
  exact (show ∀ a : ZMod 2, a+1=1 ↔ a≠1 by decide) _
lemma oddAtSub (x : Per (GridN m)) : OddAxis m (x-1) ↔ ¬ OddAxis m x := by
  have h := oddAtAdd (m:=m) (x-1); rw [sub_add_cancel] at h; tauto
lemma d_even_sep {x y} (h : OddAxis m x ↔ OddAxis m y) (e : x≠y) : 2 ≤ delta1 (GridN m) x y := by
  by_contra! hh; have hn : delta1 (GridN m) x y≠0 := fun g => e (d_equal _ _ g)
  rcases d_unit _ _ (show delta1 (GridN m) x y=1 by omega) with g|g
  · rw [g,oddAtAdd] at h; tauto
  rw [g,oddAtSub] at h; tauto
end YM.CF.Cube
