import YM.Space.Index
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

/-!
# StressSpace U1. Signed-coordinate bookkeeping

Conventions: Signed displaces the *physical* basis, the charge bit in
StressSpace's 𝔥 will be true for improper Signed. `signBit` computes orientation
(the book uses `detX`, noncomputable; identification in physics-facing module).
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction
open Function
open scoped BigOperators

/-- Even (false) → act by 1; odd (true) → act by -1. -/
def pay {α : Type*} [Neg α] (t : Bool) (a : α) : α := if t then -a else a
@[simp] theorem pay_true {α : Type*} [Neg α] (a : α) : pay true a = -a := rfl
@[simp] theorem pay_false {α : Type*} [Neg α] (a : α) : pay false a = a := rfl
@[simp] theorem pay_zero {α : Type*} [AddGroup α] (t : Bool) : pay t (0 : α) = 0 := by
  cases t <;> simp

theorem pay_comp {α : Type*} [InvolutiveNeg α] (b c : Bool) (a : α) :
    pay b (pay c a) = pay (b.xor c) a := by cases b <;> cases c <;> simp
@[simp] theorem pay_pay {α : Type*} [InvolutiveNeg α] (t : Bool) (a : α) : pay t (pay t a) = a := by
  simp [pay_comp]
theorem pay_comm {α : Type*} [InvolutiveNeg α] (b c : Bool) (a : α) :
    pay b (pay c a) = pay c (pay b a) := by simp only [pay_comp, Bool.xor_comm b]
theorem pay_add {A : Type*} [AddCommGroup A] (t : Bool) (a b : A) :
    pay t (a+b) = pay t a + pay t b := by cases t <;> simp [add_comm]
/-- Pure permutation without any flips. -/
def unsigned (p : Equiv.Perm Axis) : Signed := ⟨p, fun _ => false⟩
@[simp] theorem unsigned_one : unsigned 1 = 1 := rfl
theorem unsigned_mul (p q : Equiv.Perm Axis) : unsigned (p*q) = unsigned p * unsigned q := by
  ext <;> rfl
/-- Split a motion on input: flip first, then permute. -/
def diagonalFlip (f : Axis → Bool) : Signed := ⟨1, f⟩
theorem unsigned_flip (g : Signed) : unsigned g.perm * diagonalFlip g.flip = g := by
  cases g; apply Signed.ext
  · ext; rfl
  funext; simp [unsigned, diagonalFlip]

theorem unsigned_mirror (p : Equiv.Perm Axis) (i : Axis) :
    unsigned p * Signed.mirror i = Signed.mirror (p i) * unsigned p := by
  apply Signed.ext
  · ext; rfl
  funext j
  simp [unsigned, Signed.mirror]

theorem diagonal_induction {P : Signed → Prop} (one : P 1) (mm : ∀ i, P (Signed.mirror i))
    (hm : ∀ x y, P x → P y → P (x*y)) (f : Axis → Bool) : P (diagonalFlip f) := by
  let M (i : Axis) := if f i then Signed.mirror i else 1
  suffices diagonalFlip f = M 3 * M 2 * M 1 * M 0 by
    rw [this]; have h (i : Axis) : P (M i) := by unfold M; split_ifs <;> simp_all
    exact hm _ _ (hm _ _ (hm _ _ (h 3) (h 2)) (h 1)) (h 0)
  apply Signed.ext
  · simp only [Signed.mul_perm, M]; split_ifs <;> rfl
  funext j
  have mf i a : (M i).perm a = a := by unfold M; split_ifs <;> rfl
  have mg i a : (M i).flip a = if i=a then f a else false := by
    by_cases h : i=a
    · subst i; simp only [M]; split_ifs <;> simp_all [Signed.mirror]
    simp only [M]; split_ifs <;> simp_all [Signed.mirror]
  simp only [diagonalFlip, Signed.mul_flip, mf, mg]
  fin_cases j <;> simp

theorem signed_induction {P : Signed → Prop} (pu : ∀ p, P (unsigned p))
    (mm : ∀ i, P (Signed.mirror i)) (hm : ∀ x y, P x → P y → P (x*y)) (g : Signed) : P g := by
  have hv := hm _ _ (pu g.perm) (diagonal_induction (P:=P) (pu 1) mm hm g.flip)
  rwa [unsigned_flip] at hv

/-- Computable sign of determinant. -/
def invBit (p : Equiv.Perm Axis) : Bool :=
  (decide (p 1 ≤ p 0)).xor <|
    (decide (p 2 ≤ p 0)).xor <|
      (decide (p 2 ≤ p 1)).xor <|
        (decide (p 3 ≤ p 0)).xor ((decide (p 3 ≤ p 1)).xor (decide (p 3 ≤ p 2)))

def flips (s : Signed) : Bool :=
  (s.flip 0).xor ((s.flip 1).xor ((s.flip 2).xor (s.flip 3)))

def signBit (s : Signed) := (invBit s.perm).xor (flips s)

private lemma pay_units (b c : Bool) : pay b (1:ℤˣ) * pay c 1 = pay (b.xor c) 1 := by
  cases b <;> cases c <;> simp
private lemma pay_det_inj : Injective (fun b => pay b (1:ℤˣ)) := by
  intro b c he
  have h := congr_arg Units.val he
  cases b <;> cases c <;> norm_num at *
open Equiv.Perm
private lemma invBit_ok (p : Equiv.Perm Axis) : signAux p = pay (invBit p) 1 := by
  have h : finPairsLT 4 = {⟨1,0⟩,⟨2,0⟩,⟨2,1⟩,⟨3,0⟩,⟨3,1⟩,⟨3,2⟩} := by decide
  rw [signAux, h]
  simp (disch := decide) only [Finset.prod_insert, Finset.prod_singleton]
  simp only [show ∀ i j : Axis, (if p i ≤ p j then (-1:ℤˣ) else 1) = pay (decide (p i ≤ p j)) 1 from
    fun i j => by split_ifs with t <;> simp [t], pay_units, invBit]

private lemma flips_ok (s : Signed) : ∏ i : Axis, pay (s.flip i) (1:ℤˣ) = pay (flips s) 1 := by
  rw [show (Finset.univ : Finset Axis) = {0,1,2,3} by decide]
  simp (disch := decide) only [Finset.prod_insert, Finset.prod_singleton, pay_units, flips]

@[simp] theorem signBit_one : signBit 1 = false := by decide
theorem signBit_mul (s r : Signed) : signBit (s*r) = (signBit s).xor (signBit r) := by
  have detu : invBit (s*r).perm = (invBit s.perm).xor (invBit r.perm) := by
    apply pay_det_inj
    dsimp only
    rw [← invBit_ok, ← pay_units, ← invBit_ok, ← invBit_ok]
    exact signAux_mul s.perm r.perm
  have detf : flips (s*r) = (flips s).xor (flips r) := by
    apply pay_det_inj; dsimp only
    rw [← pay_units, ← flips_ok, ← flips_ok, ← flips_ok,
      ← Equiv.prod_comp r.perm (fun i => pay (s.flip i) (1:ℤˣ)), ← Finset.prod_mul_distrib]
    simp [Signed.mul_flip, pay_units]
  simp only [signBit, detu, detf, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem signBit_inv (s : Signed) : signBit s⁻¹ = signBit s := by
  have h := signBit_mul s⁻¹ s
  rw [inv_mul_cancel, signBit_one] at h
  cases he : signBit s⁻¹ <;> cases hh : signBit s <;> simp_all

lemma signBit_swap (i j : Axis) (h : i ≠ j) :
    signBit (unsigned (Equiv.swap i j)) = true := by
  apply pay_det_inj; dsimp only [signBit, flips, unsigned]; simp only [Bool.xor_false]
  rw [← invBit_ok, signAux_swap h, pay_true]
@[simp] lemma signBit_mirror (i : Axis) : signBit (Signed.mirror i) = true := by
  fin_cases i <;> decide
end YM.GaugeFieldConstruction
