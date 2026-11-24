import YM.CF.Cubes.Axis

/-!
Segment and grid geometry on one coordinate of the micro torus. Parameterization always
uses the manuscript's nonnegative orientation (even for wrapping intervals). These uniform
size lemmas are also used for price bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Lattice Cube Finset Function
variable {s : Side} {x y p : Per s}
variable {l a b : ℕ}

/-- Natural (positive axis) oriented distance < s. -/
def along (x y : Per s) : ℕ := (y-x).val
@[simp] theorem along_self (x : Per s) : along x x = 0 := by simp [along]
@[simp] theorem along_lt (x y : Per s) : along x y < s.val := ZMod.val_lt _
@[simp] theorem add_along (x y : Per s) : x + along x y = y := by simp [along]
theorem along_add (x : Per s) (h : l < s.val) : along x (x+l) = l := by
  rw [along,add_sub_cancel_left,ZMod.val_natCast_of_lt h]
theorem along_zero : along x y = 0 ↔ x = y := ⟨fun h => by simpa [h] using add_along x y, by rintro rfl; simp⟩
theorem add_inj_nat (ha : a < s.val) (hb : b < s.val) : x+a = x+b ↔ a=b :=
  ⟨fun h => by simpa [along_add x ha,along_add x hb] using congrArg (along x) h, by rintro rfl; rfl⟩
theorem along_succ (h : along x y + 1 < s.val) : along x (y+1) = along x y+1 := by
  rw [← along_add x h]; push_cast; rw [← add_assoc,add_along]

theorem delta_eq (x y : Per s) : delta1 s y x = min (along x y) (s.val-along x y) :=
  ZMod.valMinAbs_natAbs_eq_min _

def arc (x : Per s) (l : ℕ) := univ.filter fun y : Per s => along x y ≤ l
@[simp] theorem mem_arc : y ∈ arc x l ↔ along x y ≤ l := by simp [arc]
theorem arc_image (x : Per s) (h : l < s.val) : arc x l = (range (l+1)).image (fun i : ℕ => (x+i)) := by
  ext y
  rw [mem_arc,mem_image]
  constructor
  · intro h; exact ⟨_, mem_range.mpr (Nat.lt_succ_of_le h), add_along x y⟩
  rintro ⟨i,hi,rfl⟩
  have H := Nat.le_of_lt_succ (mem_range.mp hi)
  rwa [along_add x (H.trans_lt h)]
theorem arc_card (x : Per s) (h : l < s.val) : (arc x l).card=l+1 := by
  rw [arc_image x h,card_image_iff.mpr,card_range]
  intro i hi j hj
  exact (add_inj_nat (Nat.lt_of_lt_of_le (mem_range.mp hi) h) (Nat.lt_of_lt_of_le (mem_range.mp hj) h)).mp

theorem side_last (x : Per s) (h : l < s.val) : x+l ∈ arc x l := mem_arc.mpr (along_add _ h).le

/-- Offsets measured in a single arc. -/
theorem offset_dist (x : Per s) (h : a ≤ b) (hb : b-a < s.val) : along (x+(a : Per s)) (x+(b : Per s))=b-a := by
  rw [show x+(b:ℕ)=(x+(a : Per s))+ ((b-a:ℕ) : Per s) from by rw [add_assoc,← Nat.cast_add,Nat.add_sub_of_le h], along_add _ hb]
theorem subarc (h : a + b ≤ l) (hl : l < s.val) : arc (x+(a : Per s)) b ⊆ arc x l := by
  intro y hy
  have hh := mem_arc.mp hy
  rw [← add_along (x+(a : Per s)) y, mem_arc,add_assoc,← Nat.cast_add,along_add] <;> omega

section Grid
variable {c : Side} (g : Ratio c s)

/-- One-dimensional additive scaled embed. -/
def base (i : Per c) : Per s := g.root (fun _ => i) 0
@[simp] theorem base_apply (z : Site c) (i : Axis) : g.embed z i = base g (z i) := rfl
@[simp] theorem base_int (i : ℤ) : base g i = (g.count.val:Per s) * i := by
  let p : Cover := fun _ => i
  change g.embed (wrap _ p) 0 = _
  rw [Ratio.embed_wrap,wrap_here]
  simp [p]
@[simp] theorem base_nat (i : ℕ) : base g i = (g.count.val:Per s) * i := by exact_mod_cast base_int g i
@[simp] theorem base_add (x y : Per c) : base g (x+y) = base g x + base g y := by
  change g.root ((fun _ => x)+(fun _ => y)) 0 = _
  rw [map_add]; rfl
@[simp] theorem base_zero : base g 0 = 0 := by simpa using base_nat g 0
@[simp] theorem base_one : base g 1 = g.count.val := by simpa using base_nat g 1

theorem count_le : g.count.val ≤ s.val := g.exact_size ▸ Nat.le_mul_of_pos_left g.count.val c.property

theorem base_distance (i j : Per c) : along (base g i) (base g j) = g.count.val * along i j := by
  conv_lhs => arg 2; rw [← add_along i j,base_add,base_nat,← Nat.cast_mul]
  exact along_add _ (by rw [g.exact_size,mul_comm]; exact Nat.mul_lt_mul_of_pos_right (along_lt ..) g.count.property)

def tile (i : Per c) : Finset (Per s) := univ.filter fun x => along (base g i) x < g.count.val
@[simp] theorem mem_tile (i : Per c) : x ∈ tile g i ↔ along (base g i) x < g.count.val := by simp [tile]

@[simp] theorem subdiv_val (i : Per c) (h : a < g.count.val) : (base g i+a).val=i.val*g.count.val+a := by
  have hv : i.val*g.count.val+a < s.val := lt_of_lt_of_le (by omega : i.val*g.count.val+a < i.val*g.count.val+g.count.val)
    (by rw [← Nat.succ_mul,g.exact_size]; exact Nat.mul_le_mul_right _ (ZMod.val_lt i))
  conv_lhs => rw [← ZMod.natCast_zmod_val i, base_nat,mul_comm,← Nat.cast_mul,← Nat.cast_add]
  exact ZMod.val_natCast_of_lt hv

def block (x : Per s) : Per c := (x.val/g.count.val : ℕ)
theorem block_lt (x : Per s) : x.val/g.count.val < c.val := (Nat.div_lt_iff_lt_mul g.count.property).mpr (g.exact_size ▸ along_lt' x)
where along_lt' (x : Per s) : x.val < s.val := ZMod.val_lt _

theorem block_val (x : Per s) : (block g x).val = x.val/g.count.val := ZMod.val_natCast_of_lt (block_lt g x)
@[simp] theorem block_add (i : Per c) (ha : a < g.count.val) : block g (base g i+a) = i := by
  unfold block
  rw [subdiv_val g i ha]
  have h : (i.val*g.count.val+a)/g.count.val=i.val := by rw [Nat.mul_comm i.val,Nat.mul_add_div (show 0<g.count.val from g.count.property),Nat.div_eq_of_lt ha]; simp
  rw [h]; simp

def part (x : Per s) : Fin g.count.val := ⟨x.val%g.count.val,Nat.mod_lt x.val g.count.property⟩

@[simp] theorem glue_block (x : Per s) : base g (block g x) + ((part g x).val:Per s)=x := by
  apply ZMod.val_injective
  rw [subdiv_val g _ (part g x).isLt,block_val]
  unfold part; dsimp only; rw [Nat.mul_comm,add_comm,Nat.mod_add_div]
theorem tile_add (i : Per c) (ha : a < g.count.val) : base g i + a ∈ tile g i := by rw [mem_tile,along_add _ (ha.trans_le (count_le g))]; exact ha

theorem block_eq (x : Per s) (i : Per c) : block g x = i ↔ x ∈ tile g i := by
 constructor
 · rintro rfl; simpa only [glue_block] using tile_add g (block g x) (part g x).isLt
 intro h; convert block_add g i ((mem_tile g i).mp h) using 1; rw [add_along]

def off (x y : Per s) : Per s := y-x
/-- Partition from possibly translated origin. Used on bands wrapping the torus. -/
def origin (x : Per s) (i : Per c) := x+base g i
def tile' (x : Per s) (i : Per c) := univ.filter fun a : Per s => along (origin g x i) a < g.count.val
def owner (x y : Per s) := block g (off x y)
def stamp (x y : Per s) := part g (off x y)
def native (x : Per s) (i : Per c) (a : ℕ) : Per s := origin g x i + a

@[simp] theorem owner_native (x : Per s) (i : Per c) (ha : a < g.count.val) : owner g x (native g x i a) = i := by
 unfold native owner off origin; rw [add_assoc,add_sub_cancel_left]; exact block_add g _ ha
@[simp] theorem stamp_native (x : Per s) (i : Per c) (ha : a < g.count.val) : (stamp g x (native g x i a)).val=a := by
 unfold stamp native off origin; rw [add_assoc,add_sub_cancel_left]; unfold part; dsimp only; rw [subdiv_val g i ha,Nat.mul_add_mod', Nat.mod_eq_of_lt ha]
@[simp] theorem native_stamp (x y : Per s) : native g x (owner g x y) (stamp g x y).val = y := by
 unfold native owner stamp origin; rw [add_assoc,glue_block]; simp [off]

@[simp] theorem native_zero (x : Per s) (i : Per c) : native g x i 0=origin g x i := by simp [native]
@[simp] theorem native_last (x : Per s) (i : Per c) : native g x i g.count.val=origin g x (i+1) := by simp [native,origin,add_assoc]
lemma native_succ (x : Per s) (i : Per c) (a : ℕ) : native g x i (a+1) = native g x i a + 1 := by simp [native,add_assoc]

end Grid
end YM.CF.BProof
