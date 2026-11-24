import ExactRunning.Mode.Crate
import ExactRunning.Det.Prediction
/-! # Coarse-cell packing: projections on sums -/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix


def πl (α β : Type) (R : Type) [DecidableEq α] [Zero R] [One R] :=
  fromCols (1 : Matrix α α R) (0 : Matrix α β R)

def πr (α β : Type) (R : Type) [DecidableEq β] [Zero R] [One R] :=
  fromCols (0 : Matrix β α R) (1 : Matrix β β R)

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {R : Type} [Semiring R]

lemma πl_vec (v : α ⊕ β → R) : πl α β R *ᵥ v = v ∘ Sum.inl := by
  simp [πl,fromCols_mulVec]
lemma πr_vec (v : α ⊕ β → R) : πr α β R *ᵥ v = v ∘ Sum.inr := by
  simp [πr,fromCols_mulVec]

namespace Tub
variable (ι : Type) [Fintype ι] [DecidableEq ι] (P Q : Crate)

def fst :
    Tub ι P (P.pair Q) (fun m _ => πl (P.key m) (Q.key m) ℝ) :=
  Tub.stock ι P (P.pair Q) _ (fun _ => πl P.tile Q.tile ℂ) ⟨1,zero_lt_one,Poster.web _⟩ <| by
    intro m a _ _ v
    rw [add_zero,πl_vec]

    let e := (P.pair Q).pack m
    let x := tune a v
    have hu : approached (πl (P.key m) (Q.key m) ℝ) = πl _ _ ℂ := by
      ext i (j|j) <;> simp [approached,πl,one_apply,apply_ite]

    change repackM (P.pack m) e (approached (πl (P.key m) (Q.key m) ℝ)) *ᵥ x = _
    rw [hu, ← show x ∘ e ∘ e.symm = x from by ext; simp, ← Function.comp_assoc, repack_act, πl_vec]
    ext ⟨i,j⟩
    have hy : e (.inl ((P.pack m).symm (i,j)))=(i,.inl j) := by
      simp [e,Crate.pair]
    simp only [Function.comp_apply,hy]
    rfl

def snd :
    Tub ι Q (P.pair Q) (fun m _ => πr (P.key m) (Q.key m) ℝ) :=
  Tub.stock ι Q (P.pair Q) _ (fun _ => πr P.tile Q.tile ℂ) ⟨1,zero_lt_one,Poster.web _⟩ <| by
    intro m a _ _ v
    rw [add_zero,πr_vec]

    let e := (P.pair Q).pack m
    let x := tune a v
    have hu : approached (πr (P.key m) (Q.key m) ℝ) = πr _ _ ℂ := by
      ext i (j|j) <;> simp [approached,πr,one_apply,apply_ite]

    change repackM (Q.pack m) e (approached (πr (P.key m) (Q.key m) ℝ)) *ᵥ x = _
    rw [hu, ← show x ∘ e ∘ e.symm = x from by ext; simp, ← Function.comp_assoc, repack_act, πr_vec]
    ext ⟨i,j⟩
    have hy : e (.inr ((Q.pack m).symm (i,j)))=(i,.inr j) := by
      simp [e,Crate.pair]
    simp only [Function.comp_apply,hy]
    rfl

@[simp] lemma fst_symb (q : Momentum) : (fst ι P Q).symb q = πl P.tile Q.tile ℂ := rfl
@[simp] lemma snd_symb (q : Momentum) : (snd ι P Q).symb q = πr P.tile Q.tile ℂ := rfl


variable {ι P Q} {S : Crate}
variable {u : Filling ι S P} {v : Filling ι S Q}

private lemma cols_add {γ : Type} (a : Matrix γ α R) (b : Matrix γ β R) :
    a * πl _ β R + b * πr α _ R = fromCols a b := by
  rw [πl,πr,mul_fromCols,mul_fromCols]
  ext i (k|k) <;> simp

def cols (A : Tub ι S P u) (B : Tub ι S Q v) :
    Tub ι S (P.pair Q) (fun m z => fromCols (u m z) (v m z)) :=
  ((A.mul (fst ι P Q)).plus (B.mul (snd ι P Q))).shift
    (fun _ => Filter.Eventually.of_forall fun _ => cols_add _ _)

@[simp] lemma cols_symb (A : Tub ι S P u) (B : Tub ι S Q v) (p : Momentum) :
    (A.cols B).symb p = fromCols (A.symb p) (B.symb p) := by
  simp [cols, cols_add]

variable {x : Filling ι P S} {y : Filling ι Q S}
private lemma rows_add {γ : Type} (a : Matrix α γ R) (b : Matrix β γ R) :
    (πl _ β R)ᵀ * a + (πr α _ R)ᵀ * b = fromRows a b := by
  simp only [πl,πr,transpose_fromCols,fromRows_mul]
  ext (k|k) j <;> simp

@[simp] lemma tr_symb (X : Tub ι S P u) (p : Momentum) :
    X.tr.symb p = (X.symb (-p))ᵀ := rfl

def rows (A : Tub ι P S x) (B : Tub ι Q S y) :
    Tub ι (P.pair Q) S (fun m z => fromRows (x m z) (y m z)) :=
  (((fst ι P Q).tr.mul A).plus ((snd ι P Q).tr.mul B)).shift
    (fun _ => Filter.Eventually.of_forall fun _ => rows_add _ _)

@[simp] lemma rows_symb (A : Tub ι P S x) (B : Tub ι Q S y) (p : Momentum) :
    (A.rows B).symb p = fromRows (A.symb p) (B.symb p) := by
  simp [rows, rows_add]

variable {T : Crate} {a : Filling ι T P} {b : Filling ι T Q}
def blocks (U : Tub ι S P u) (V : Tub ι S Q v) (A : Tub ι T P a) (B : Tub ι T Q b) :
    Tub ι (S.pair T) (P.pair Q) (fun m z => fromBlocks (u m z) (v m z) (a m z) (b m z)) :=
  (rows (cols U V) (cols A B)).shift
    (fun _ => Filter.Eventually.of_forall fun _ => fromRows_fromCols_eq_fromBlocks ..)

@[simp] lemma blocks_symb (U : Tub ι S P u) (V : Tub ι S Q v) (A : Tub ι T P a) (B : Tub ι T Q b)
    (p : Momentum) :
    (U.blocks V A B).symb p =
      fromBlocks (U.symb p) (V.symb p) (A.symb p) (B.symb p) := by
  simp only [blocks, shift_symb, rows_symb, cols_symb,fromRows_fromCols_eq_fromBlocks]

variable (ι S Q)
def nil : Tub ι Q S (fun _ _ => 0) :=
  stock ι Q S (fun _ => 0) 0 ⟨1,zero_lt_one,Poster.web _⟩ (fun m => by
    rw [show approached (repackM (Q.pack m) (S.pack m)
      (0:Matrix (Q.key m) (S.key m) ℝ)) =0 by ext; simp [repackM,approached]]
    exact Jaunt.zero _)

@[simp] lemma nil_symb (p : Momentum) : (nil ι Q S).symb p = 0 := rfl

end Tub
end ExactRunning
