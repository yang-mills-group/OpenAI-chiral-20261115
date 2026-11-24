import GaugeFieldConstruction.Signs
import Mathlib.Data.Prod.Lex

/-!
# Raw labels of the U1 calculation

For one row g/f/x and one homogeneous degree. No on-shell identifications in
these labels. The `f4` and `f5` labels use S=∂^C+∂^R and L'=∂^R-∂^C,
with the axial sign for every L' and also for B_i. A Mixed label is the B-F
label (at degree five) with *no* axial sign because we work in the
Lie-insertion copy of that row. These are complex label spaces.
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction
open Function

/-- Action of signed permutations with another sign, i.e.
 monomial representation on span of the labels. Input-index convention. -/
structure Labels (α : Type*) where
  move : Signed → α → α
  cost : Signed → α → Bool
  move_one (i : α) : move 1 i=i
  cost_one (i : α) : cost 1 i=false
  move_mul (g h : Signed) (i : α) : move (g*h) i=move g (move h i)
  cost_mul (g h : Signed) (i : α) : cost (g*h) i=(cost g (move h i)).xor (cost h i)

namespace Labels
variable {α β : Type*} (A : Labels α) (B : Labels β)
attribute [simp] move_one cost_one

@[simp] lemma move_inv (g : Signed) (i : α) : A.move g (A.move g⁻¹ i)=i := by
  rw [← move_mul]; simp
@[simp] lemma inv_move (g : Signed) (i : α) : A.move g⁻¹ (A.move g i)=i := by
  rw [← move_mul]; simp
@[simp] lemma cost_inv (g : Signed) (i : α) : A.cost g (A.move g⁻¹ i) = A.cost g⁻¹ i := by
  have h := A.cost_mul g g⁻¹ i
  cases hh : A.cost g (A.move g⁻¹ i) <;> cases he : A.cost g⁻¹ i <;> simp_all
@[simp] lemma inv_cost (g : Signed) (i : α) : A.cost g⁻¹ (A.move g i) = A.cost g i := by
  have h := A.cost_inv g⁻¹ i; rw [inv_inv] at h; exact h

def equivMove (g : Signed) : Equiv.Perm α where
  toFun := A.move g; invFun := A.move g⁻¹
  left_inv := A.inv_move g; right_inv := A.move_inv g

theorem inj (g : Signed) : Injective (A.move g) := (A.equivMove g).injective

def unitL (α : Type*) : Labels α where
  move _ := id; cost _ _ := false
  move_one _ := rfl; cost_one _ := rfl; move_mul _ _ _ := rfl; cost_mul _ _ _ := rfl

def twist : Labels α where
  move := A.move
  cost g i := (signBit g).xor (A.cost g i)
  move_one := A.move_one; move_mul := A.move_mul
  cost_one _ := by simp
  cost_mul g h i := by
    simp only [signBit_mul, cost_mul, Bool.xor_assoc, Bool.xor_left_comm]

def tensorProd : Labels (α × β) where
  move g p := (A.move g p.1,B.move g p.2)
  cost g p := (A.cost g p.1).xor (B.cost g p.2)
  move_one _ := by simp
  move_mul g h x := Prod.ext (A.move_mul ..) (B.move_mul ..)
  cost_one _ := by simp
  cost_mul g h x := by simp only [cost_mul, Bool.xor_assoc, Bool.xor_left_comm]

def directSum : Labels (α ⊕ β) where
  move g := Sum.map (A.move g) (B.move g)
  cost g := Sum.elim (A.cost g) (B.cost g)
  move_one
    | Sum.inl a => by simp
    | Sum.inr b => by simp
  cost_one
    | Sum.inl a => A.cost_one a
    | Sum.inr b => B.cost_one b
  move_mul g h
    | Sum.inl a => by simp only [move_mul, Sum.map_inl]
    | Sum.inr b => by simp only [move_mul, Sum.map_inr]
  cost_mul g h
    | Sum.inl a => A.cost_mul g h a
    | Sum.inr b => B.cost_mul g h b
end Labels
variable {α : Type*}

abbrev PairUp (α : Type*) [LE α] := {p : α × α // p.1 ≤ p.2}
abbrev Blade (α : Type*) [LT α] := {p : α × α // p.1 < p.2}
section Linear
variable [LinearOrder α]

/-- `ordered` of a pair already equal can use either sorting. -/
def ordered (a b : α) : PairUp α :=
  if h:b<a then ⟨(b,a),h.le⟩ else ⟨(a,b),le_of_not_gt h⟩

theorem ordered_swap (a b : α) : ordered a b = ordered b a := by
  unfold ordered; apply Subtype.ext; split_ifs <;> simp_all
  · order
  · constructor <;> order
@[simp] theorem ordered_same (i : PairUp α) : ordered i.val.1 i.val.2 = i := by
  unfold ordered; rw [dif_neg (not_lt.mpr i.property)]

def blade (a b : α) (h : a≠b) : Blade α :=
  if w:b<a then ⟨(b,a),w⟩ else ⟨(a,b),lt_of_le_of_ne (le_of_not_gt w) h⟩

theorem blade_swap (a b : α) (h : a≠b) : blade a b h = blade b a (Ne.symm h) := by
  unfold blade; apply Subtype.ext; split_ifs <;> simp_all
  all_goals order
@[simp] theorem blade_same (i : Blade α) (h : i.val.1 ≠ i.val.2) : blade i.val.1 i.val.2 h = i := by
  unfold blade; rw [dif_neg (not_lt.mpr i.property.le)]

namespace Labels
variable (A : Labels α)
private def symM (g : Signed) (p : PairUp α) := ordered (A.move g p.val.1) (A.move g p.val.2)
private lemma symMv (g : Signed) (i j : α) : A.symM g (ordered i j) = ordered (A.move g i) (A.move g j) := by
  rw [ordered]
  split_ifs with h
  · exact ordered_swap ..
  rfl

def symmetric : Labels (PairUp α) where
  move := A.symM
  cost g p := (A.cost g p.val.1).xor (A.cost g p.val.2)
  move_one p := by simp [symM]
  move_mul g h p := by
    change ordered _ _ = A.symM g (ordered _ _); simp only [symMv, move_mul]
  cost_one p := by simp
  cost_mul g h p := by
    simp only [cost_mul, symM, ordered]; split_ifs <;>
      simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

/-- Whether to swap two indices while sorting. -/
def reverseBit (a b : α) := decide (b<a)
private def skewM (g : Signed) (p : Blade α) :=
  blade (A.move g p.val.1) (A.move g p.val.2) ((A.inj g).ne p.property.ne)
private lemma skewMv (g : Signed) (i j : α) (h : i ≠ j) :
    A.skewM g (blade i j h) = blade (A.move g i) (A.move g j) ((A.inj g).ne h) := by
  rw [blade]; split_ifs
  · exact blade_swap ..
  rfl
private lemma rev_comp (u v : Signed) (a b : α) (hne : a≠b) :
    let p := blade (A.move v a) (A.move v b) ((A.inj v).ne hne)
    reverseBit (A.move (u*v) a) (A.move (u*v) b) =
      (reverseBit (A.move u p.val.1) (A.move u p.val.2)).xor (reverseBit (A.move v a) (A.move v b)) := by
  unfold reverseBit blade; split_ifs with ht
  · have hv := (A.inj u).ne ((A.inj v).ne hne)
    simp only [move_mul]
    apply Eq.symm
    rcases lt_or_gt_of_ne hv with L | L
    · simp [L, ht, not_lt.mpr L.le]
    · simp [L, ht, not_lt.mpr L.le]
  simp [ht, move_mul]

def exterior : Labels (Blade α) where
  move := A.skewM
  cost g p := (reverseBit (A.move g p.val.1) (A.move g p.val.2)).xor
    ((A.cost g p.val.1).xor (A.cost g p.val.2))
  move_one p := by simp [skewM]
  move_mul g h p := by
    have hv (q : Signed) : A.skewM q p = blade _ _ ((A.inj q).ne p.property.ne) := rfl
    rw [hv h, hv (g*h), skewMv]
    simp only [A.move_mul]
  cost_one p := by simp [reverseBit, not_lt.mpr p.property.le]
  cost_mul g h p := by
    have he :
        (A.cost g (A.skewM h p).val.1).xor (A.cost g (A.skewM h p).val.2) =
        (A.cost g (A.move h p.val.1)).xor (A.cost g (A.move h p.val.2)) := by
      unfold skewM blade; split_ifs <;> simp only [Bool.xor_comm]
    rw [he, rev_comp A g h _ _ p.property.ne, A.cost_mul, A.cost_mul]
    have hv (a b c d e f : Bool) : (((a.xor b).xor ((c.xor d).xor (e.xor f)))) = ((a.xor (c.xor e)).xor (b.xor (d.xor f))) := by
      cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl
    exact hv _ _ _ _ _ _
@[simp] lemma sym_mv (g) (p : PairUp α) : A.symmetric.move g p =
    ordered (A.move g p.val.1) (A.move g p.val.2) := rfl
@[simp] lemma sym_fee (g) (p : PairUp α) : A.symmetric.cost g p =
    (A.cost g p.val.1).xor (A.cost g p.val.2) := rfl
@[simp] lemma wed_mv (g) (p : Blade α) : A.exterior.move g p =
    blade (A.move g p.val.1) (A.move g p.val.2) ((A.inj g).ne p.property.ne) := rfl
@[simp] lemma wed_fee (g) (p : Blade α) : A.exterior.cost g p =
    (reverseBit (A.move g p.val.1) (A.move g p.val.2)).xor
      ((A.cost g p.val.1).xor (A.cost g p.val.2)) := rfl
end Labels
end Linear

namespace Raw

def v : Labels Axis where
  move s i := s.perm i; cost g i := g.flip i
  move_one _ := rfl; cost_one _ := rfl; move_mul _ _ _ := rfl; cost_mul _ _ _ := rfl
@[simp] lemma v_cost (s : Signed) (i : Axis) : v.cost s i=s.flip i := rfl
@[simp] lemma v_move (s : Signed) (i : Axis) : v.move s i=s.perm i := rfl

-- Use a named type for supplying the required lex order consistently.
/-- Gauge wedge indices a < b. -/
def Wed := Blade Axis
deriving Fintype, DecidableEq

def Wed.mk (a b : Axis) (h : a<b) : Wed := (⟨(a,b),h⟩ : Blade Axis)
def Wed.toBlade (w : Wed) : Blade Axis := w
instance wedOrder : LinearOrder Wed :=
  LinearOrder.lift' (fun w : Wed => toLex w.toBlade.val) (Subtype.val_injective)

def wedAct : Labels Wed := v.exterior
abbrev Sym := PairUp Axis
def symAct : Labels Sym := v.symmetric
abbrev VS := Axis × Sym
def vsAct : Labels VS := v.tensorProd symAct
abbrev G4 := PairUp Wed
abbrev G5 := Wed × Wed × Axis
abbrev F3 := Axis
/-- order types L', S -/
abbrev F4 := Axis × (Axis ⊕ Axis)
/-- order types L'L', SS, SL' -/
abbrev F5 := Axis × (Sym ⊕ Sym ⊕ (Axis × Axis))
abbrev X5 := Axis × Wed

def g4Act : Labels G4 := wedAct.symmetric
def g5Act : Labels G5 := wedAct.tensorProd (wedAct.tensorProd v)
def f3Act := v.twist
def f4Act : Labels F4 := v.twist.tensorProd (v.twist.directSum v)
def f5Act : Labels F5 := v.twist.tensorProd
  (v.twist.symmetric.directSum (symAct.directSum (v.tensorProd v.twist)))
def x5Act := v.tensorProd wedAct
end Raw
end YM.GaugeFieldConstruction
