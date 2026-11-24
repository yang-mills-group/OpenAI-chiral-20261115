import YM.CF.Cubes.Axis

/-! Integer anchor interpolation with copiable collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat
variable {m B : Side}
lemma grid_has (m : Side) : 4≤(GridN m).val := by
  simp only [GridN,natM]; have h : 0 < m.val := m.property; omega
lemma enough (m B : Side) : 4*B.val≤(Domain m B).val := by
  rw [(scaleR m B).exact_size]; exact Nat.mul_le_mul_right _ (grid_has m)
lemma d_small (x : Per (Domain m B)) (i : ℤ) (h : i.natAbs≤B.val) : delta1 (Domain m B) (x+i) x=i.natAbs := by
  unfold delta1; rw [add_sub_cancel_left]
  congr 1; apply (ZMod.valMinAbs_spec _ _).mpr; exact ⟨rfl,by rw [Set.mem_Ioc]; have he := enough m B; have ht : 0 < B.val := B.property; omega⟩
lemma links_d (x : Per (Domain m B)) : delta1 (Domain m B) (x+1) x=1 := by
  have he := d_small x 1 (show (1:ℤ).natAbs≤B.val from B.property); simpa using he
lemma local_coords (x : Per (Domain m B)) : ∃ a : Per (GridN m), ∃ j : ℤ, 0≤j ∧ j < B.val ∧ x=high m B a+j := by
  let q : ℤ := x.valMinAbs / B.val; let j : ℤ := x.valMinAbs % B.val
  have hb : 0 < (B.val:ℤ) := by exact_mod_cast B.property
  refine ⟨(q:ℤ),j, Int.emod_nonneg _ hb.ne',Int.emod_lt_of_pos _ hb,?_⟩
  rw [high_cast,← Int.cast_add,show B.val*q+j=x.valMinAbs from Int.mul_ediv_add_emod ..,ZMod.coe_valMinAbs]

def collar (B : Side) := B.val/4
def width (B : Side) := B.val-collar B
lemma collar_lt (B : Side) : collar B < B.val := by have h : 0 < B.val := B.property; unfold collar; omega
lemma enoughWidth (B : Side) : width B + collar B=B.val := Nat.sub_add_cancel (collar_lt B).le
lemma width_big (B : Side) : B.val ≤ 2*width B := by have h := enoughWidth B; unfold collar at h; omega
lemma width_pos (B : Side) : 0<width B := Nat.sub_pos_of_lt (collar_lt B)
abbrev Coin (B : Side) := Fin (width B)
-- enc θ=t.val+1. even radius r+t, odd S-t-1
def radius (m B : Side) (a : Per (GridN m)) (t : Coin B) := if OddAxis m a then width B-(t.val+1) else collar B+t.val
def elect (m B : Side) (x : Per (Domain m B)) (t : Coin B) (a : Per (GridN m)) :=
    delta1 (Domain m B) x (high m B a) ≤ radius m B a t
instance (x t a) : Decidable (elect m B x t a) := by unfold elect; infer_instance
lemma radius_lt (m B : Side) (a t) : radius m B a t < B.val := by
  have h := t.isLt; have he := enoughWidth B; unfold radius; split <;> omega
lemma elect_some (m B : Side) (x : Per (Domain m B)) (t : Coin B) : ∃ a, elect m B x t a := by
  obtain ⟨a,j,h0,h,xh⟩ := local_coords x
  have ht : delta1 (Domain m B) x (high m B a)=j.natAbs := by rw [xh,d_small (m:=m) (B:=B) _ j (by omega)]
  have he : delta1 (Domain m B) x (high m B (a+1))=(j-(B.val:ℤ)).natAbs := by
    rw [show x=high m B (a+1)+(↑(j-B.val):Per (Domain m B)) by rw [xh,high_inc]; push_cast; abel,d_small _ _ (by omega)]
  have hb : radius m B a t+radius m B (a+1) t=B.val-1 := by
    have h := t.isLt; have k := enoughWidth B; unfold radius; by_cases g:OddAxis m a <;> simp only [oddAtAdd,g,ite_true,ite_false,not_true,not_false_eq_true] <;> omega
  by_cases e : elect m B x t a; exact ⟨_,e⟩
  refine ⟨a+1,?_⟩; unfold elect at *; have g := B.property; omega
lemma elect_unique {x a b t} (h : elect m B x t a) (g : elect m B x t b) : a=b := by
  by_contra e
  have hi : B.val * delta1 (GridN m) a b ≤ radius m B a t+radius m B b t := by
    rw [←d_high]; exact (d_one_triangle _ x _).trans (add_le_add (by rw [d_sym]; exact h) g)
  by_cases hz : OddAxis m a ↔ OddAxis m b
  · have ho := Nat.mul_le_mul_left B.val (d_even_sep hz e)
    have ht := radius_lt m B a t; have hv := radius_lt m B b t; omega
  have hp : 0<delta1 (GridN m) a b := Nat.pos_of_ne_zero (fun H => e (d_equal _ _ H))
  have ht := t.isLt; have hb := enoughWidth B; have he := Nat.mul_le_mul_left B.val (Nat.succ_le_of_lt hp)
  unfold radius at hi; split at hi <;> split at hi <;> first | contradiction | omega | tauto
lemma elect_close {x a b t u} (h : elect m B x t a) (g : elect m B x u b) : delta1 (GridN m) a b ≤ 1 := by
  by_contra! e
  have hi : delta1 _ (high m B a) (high m B b)< B.val+B.val :=
    lt_of_le_of_lt (d_one_triangle _ x _) (add_lt_add (by rw [d_sym]; exact lt_of_le_of_lt h (radius_lt ..)) (lt_of_le_of_lt g (radius_lt ..)))
  rw [d_high] at hi; have he := Nat.mul_le_mul_left B.val (show 2≤delta1 (GridN m) a b from e); omega
lemma elect_mon {x a b} {t u : Coin B} (h : elect m B x t a) (g : elect m B x u b) (ht : t.val≤u.val) :
    a=b ∨ (OddAxis m a ∧ ¬ OddAxis m b ∧ delta1 (GridN m) a b≤1) := by
  by_cases he : a=b; exact Or.inl he
  right
  have ha : OddAxis m a := by
    by_contra hx; apply he; apply elect_unique _ g
    unfold elect at *; apply h.trans; simp [radius,hx,ht]
  have hr := elect_close h g
  exact ⟨ha,fun H => not_le_of_gt (show delta1 (GridN m) a b < 2 from Nat.lt_succ_of_le hr) (d_even_sep (iff_of_true ha H) he),hr⟩
end YM.CF.Cube
