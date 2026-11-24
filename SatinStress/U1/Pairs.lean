import SatinStress.U1.Slot

/-!
# Sorted pair slots

For antisymmetric indices we only need the 6 wedge components in four dimensions.
Use a four-axis `Blade`, sorted with strict inequality.
Also implement symmetric pairs of arbitrary Slot uniformly (in this calculation needed
for symmetric **axes** and for the Bose pair of **field strengths**).
-/

namespace SatinStress.U1

open List

abbrev Duo (α : Type) [LE α] := { ij : α × α // ij.1 ≤ ij.2 }
namespace Duo
variable {α : Type} [LinearOrder α]

def sym (i j : α) : Duo α := if h : i ≤ j then ⟨(i,j),h⟩ else ⟨(j,i),(le_of_not_ge h)⟩
lemma sym_eq {i j : α} (h : i ≤ j) : sym i j = ⟨(i,j),h⟩ := by simp only [sym, dif_pos h]
@[simp]
lemma sym_own (x : Duo α) : sym x.val.1 x.val.2 = x := by rw [sym_eq x.property]
lemma sym_comm (a b : α) : sym a b = sym b a := by
  unfold sym
  rcases lt_trichotomy a b with h | he | h
  · simp only [h.le, ↓reduceDIte, not_le.mpr h]
  · subst b; rfl
  · simp only [h.le, ↓reduceDIte, not_le.mpr h]
lemma induction2 {P : Duo α → Prop} (H : ∀ a b : α, P (sym a b)) (x : Duo α) : P x := by
  simpa only [sym_own] using H x.val.1 x.val.2

def act (S : Slot α) (p : Motion) (x : Duo α) : Duo α :=
  sym (S.mv p x.val.1) (S.mv p x.val.2)
@[simp]
lemma act_sym (S : Slot α) (p : Motion) (i j : α) :
    act S p (sym i j) = sym (S.mv p i) (S.mv p j) := by
  obtain h | h := le_total i j
  · rw [sym_eq h]; rfl
  rw [sym_comm i, sym_eq h, sym_comm (S.mv p i)]; rfl

def mass (S : Slot α) (p : Motion) (x : Duo α) := S.factor p x.val.1 * S.factor p x.val.2
@[simp]
lemma mass_sym (S : Slot α) (p : Motion) (i j : α) : mass S p (sym i j) = S.factor p i * S.factor p j := by
  obtain h | h := le_total i j
  · rw [sym_eq h]; rfl
  rw [sym_comm i, sym_eq h,mul_comm]; rfl

def inds (S : Slot α) (x : Duo α) := S.inds x.val.1 ++ S.inds x.val.2
lemma inds_sym (S : Slot α) (i j : α) : (inds S (sym i j)).Perm (S.inds i ++ S.inds j) := by
  obtain h | h := le_total i j
  · rw [sym_eq h]; exact .refl _
  rw [sym_comm i, sym_eq h]; exact List.perm_append_comm

def detPower (S : Slot α) (x : Duo α) := S.detPower x.val.1 + S.detPower x.val.2
@[simp] lemma detPower_sym (S : Slot α) (a b : α) :
    detPower S (sym a b) = S.detPower a + S.detPower b := by
  obtain h | h := le_total a b
  · rw [sym_eq h]; rfl
  rw [sym_comm a, sym_eq h, add_comm]; rfl

@[simps]
def slot (S : Slot α) : Slot (Duo α) where
  mv := act S
  mv_id x := by apply induction2 (x:=x); simp
  mv_mul p q x := by apply induction2 (x:=x); simp
  factor := mass S
  factor_id x := by simp [mass]
  factor_mul p q x := by
    apply induction2 (x:=x)
    intro a b
    simp
    ac_rfl
  inds := inds S
  inds_mv p x := by
    apply induction2 (x:=x)
    intro a b
    rw [act_sym]
    apply (inds_sym S _ _).trans; apply Perm.trans _ ((inds_sym S a b).symm.map p)
    rw [map_append]; exact (S.inds_mv p a).append (S.inds_mv p b)
  detPower := detPower S
  detPower_mv p x := by apply induction2 (x:=x); simp

/-- Enumerate `≤` pairs. -/
def enumerate (e : List α) : List (Duo α) :=
  e.flatMap fun a => e.filterMap fun b => if h : a ≤ b then some ⟨(a,b),h⟩ else none
lemma mem_enumerate {e : List α} (h : ∀ i, i ∈ e) (x : Duo α) : x ∈ enumerate e := by
  apply List.mem_flatMap.mpr
  refine ⟨x.val.1,h _,List.mem_filterMap.mpr ⟨x.val.2,h _,dif_pos x.property⟩⟩
end Duo

@[ext]
structure Blade where
  val : Axis × Axis
  property : val.1 < val.2

namespace Blade

def key (x : Blade) : ℕ := 4*x.val.1.val + x.val.2.val
lemma key_inj : Function.Injective key := by
  rintro ⟨⟨i,j⟩,hij⟩ ⟨⟨a,b⟩,hab⟩ h
  dsimp [key] at h
  obtain rfl : i = a := Fin.ext (by omega)
  obtain rfl : j = b := Fin.ext (by omega)
  rfl
-- Give it a dedicated order for gauge-gauge (Bose) pair.
instance linOrder : LinearOrder Blade := LinearOrder.lift' key key_inj


-- Enumeration of just Blade

def enumerate : List Blade := axes.flatMap fun i => axes.filterMap fun j =>
  if h : i < j then some ⟨(i,j),h⟩ else none
lemma mem_enumerate (x : Blade) : x ∈ enumerate := List.mem_flatMap.mpr
  ⟨_, mem_axes x.val.1, List.mem_filterMap.mpr ⟨_, mem_axes x.val.2, dif_pos x.property⟩⟩

def pack (i j : Axis) (h : i ≠ j) : Blade :=
  if h' : i < j then ⟨(i,j), h'⟩ else ⟨(j,i), h.lt_or_gt.resolve_left h'⟩
@[simp] lemma pack_of_lt {i j : Axis} (h : i < j) : pack i j h.ne = ⟨(i,j),h⟩ :=
  dif_pos h
@[simp] lemma pack_of_gt {i j : Axis} (h : j < i) : pack i j h.ne' = ⟨(j,i),h⟩ :=
  dif_neg (not_lt.mpr h.le)
lemma pack_comm (i j : Axis) (h : i ≠ j) : pack i j h = pack j i (Ne.symm h) := by
  rcases h.lt_or_gt with h|h
  · rw [pack_of_lt h, pack_of_gt h]
  · rw [pack_of_lt h, pack_of_gt h]
lemma induction2 {P : Blade → Prop} (H : ∀ a b : Axis, ∀ h : a<b, P ⟨(a,b),h⟩) (x : Blade) : P x :=
  H x.val.1 x.val.2 x.property

def act (p : Motion) (x : Blade) : Blade :=
  pack (p x.val.1) (p x.val.2) (p.injective.ne x.property.ne)
@[simp] lemma act_pack (p : Motion) (i j : Axis) (h : i ≠ j) :
    act p (pack i j h) = pack (p i) (p j) (p.injective.ne h) := by
  rcases h.lt_or_gt with h|h
  · rw [pack_of_lt h]; rfl
  rw [pack_of_gt h, pack_comm (p i)]; rfl
@[simp]
lemma act_id (x : Blade) : act 1 x = x := pack_of_lt x.property
lemma act_mul (p q : Motion) (x : Blade) : act (p*q) x = act p (act q x) := by
  change _ = act p (pack _ _ _)
  rw [act_pack]; rfl

def mass (p : Motion) (x : Blade) : ℤˣ := if p x.val.1 < p x.val.2 then 1 else -1
@[simp] lemma mass_id (x : Blade) : mass 1 x = 1 := if_pos x.property
lemma mass_mul (p q : Motion) (x : Blade) : mass (p*q) x = mass p (act q x) * mass q x := by
  rcases (q.injective.ne x.property.ne).lt_or_gt with h|h
  · simp only [act,pack_of_lt h,mass,Equiv.Perm.mul_apply,h,↓reduceIte,mul_one]; rfl
  rw [act,pack_of_gt h]
  rcases (p.injective.ne h.ne).lt_or_gt with H|H <;>
    simp [mass,H,h.not_gt,H.not_gt]

def inds (x : Blade) := [x.val.1,x.val.2]
lemma inds_act (p : Motion) (x : Blade) : (inds (act p x)).Perm ((inds x).map p) := by
  rcases (p.injective.ne x.property.ne).lt_or_gt with h|h
  · rw [act,pack_of_lt h]; exact .refl _
  rw [act,pack_of_gt h]; exact .swap (p x.val.1) (p x.val.2) []

@[simps]
def slot : Slot Blade where
  mv := act
  mv_id := act_id
  mv_mul := act_mul
  factor := mass
  factor_id := mass_id
  factor_mul := mass_mul
  inds := inds
  inds_mv := inds_act
  detPower _ := 0
  detPower_mv _ _ := rfl
end Blade
end SatinStress.U1
