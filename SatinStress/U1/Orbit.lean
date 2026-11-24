import SatinStress.U1.Slot
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.List.Count
import Mathlib.Data.List.Dedup
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi

/-!
# Orbit theorem for the raw (93) columns

The list of reps is executable (in particular computes actual omissions).
The span theorem uses the raw coefficient equations, not taking a dimension
of the uncomputed invariant space as an input. Pairs in the same orbit
come in only once in `pieces`, without a stabilizer factor.
-/

namespace SatinStress.U1.Slot
open Finset Equiv.Perm Function
open scoped BigOperators

variable {α : Type} (S : Slot α)

-- Sign flip criterion (test for each coordinate reflection).
def parity (a : α) : Bool := axes.all fun i => ((S.inds a).count i + S.detPower a) % 2 == 0
lemma parity_iff (a : α) : S.parity a = true ↔
    ∀ i : Axis, ((S.inds a).count i + S.detPower a) % 2 = 0 := by simp [parity]
@[simp] lemma parity_mv (p : Motion) (a : α) : S.parity (S.mv p a) = S.parity a := by
  have e i : (S.inds (S.mv p a)).count (p i) = (S.inds a).count i :=
    ((S.inds_mv p a).count_eq _).trans (List.count_map_of_injective _ p p.injective _)
  apply Bool.eq_iff_iff.mpr
  rw [S.parity_iff, S.parity_iff, S.detPower_mv]
  constructor
  · intro h i; simpa [e] using h (p i)
  · intro h i; obtain ⟨i,rfl⟩ := p.surjective i; rw [e]; exact h i

section
variable (K : Type*) [Field K]
/-- The raw coefficient subspace, before the on-shell projection. This
    uses the signed-permutation tensor transformations in U1. -/
def invariant : Submodule K (α → K) where
  carrier x := (∀ a, x a ≠ 0 → S.parity a = true) ∧
    ∀ p a, x (S.mv p a) = (↑(S.factor p a) : ℤ) • x a
  add_mem' {x y} hx hy := by
    rcases hx with ⟨hx₁,hx₂⟩; rcases hy with ⟨hy₁,hy₂⟩
    constructor
    · intro a h; by_cases hz : x a = 0
      · exact hy₁ a (fun he => by simp [hz,he] at h)
      exact hx₁ a hz
    intro p a; simp [hx₂,hy₂,smul_add]
  smul_mem' c x hx := by
    rcases hx with ⟨h₁,h₂⟩; refine ⟨fun a h => h₁ a fun z => ?_, fun p a => ?_⟩
    · simp [z] at h
    simp only [Pi.smul_apply,h₂]; exact smul_comm ..
  zero_mem' := by
    constructor <;> simp

variable {K}
lemma mem_invariant (x : α → K) : x ∈ S.invariant K ↔
    (∀ a, x a ≠ 0 → S.parity a = true) ∧ ∀ p a, x (S.mv p a) = (↑(S.factor p a) : ℤ) • x a := Iff.rfl
end

variable [DecidableEq α]

/-- There is no sign ambiguity in assigning to the orbit. -/
def permits (a : α) : Bool := S.parity a &&
  motions.all fun p => decide (S.mv p a = a → S.factor p a = 1)
lemma permits_iff (a : α) : S.permits a = true ↔
    S.parity a = true ∧ ∀ p, S.mv p a = a → S.factor p a = 1 := by
  simp only [permits, Bool.and_eq_true,List.all_eq_true,mem_motions,decide_eq_true_eq, true_imp_iff]
lemma consistent (a : α) (h : S.permits a) (p q : Motion) (e : S.mv p a = S.mv q a) :
    S.factor p a = S.factor q a := by
  have h' : S.mv (p⁻¹*q) a = a := by rw [mv_mul, ← e, ← mv_mul, inv_mul_cancel, mv_id]
  have t := ((S.permits_iff a).mp h).2 (p⁻¹*q) h'
  nth_rw 1 [show q = p * (p⁻¹ * q) from (mul_inv_cancel_left ..).symm] 
  rw [factor_mul,h',t,mul_one]

/-- distinct positions of an orbit (no repeats) -/
def locations (a : α) := List.dedup (motions.map (fun p => S.mv p a))
@[simp]
lemma mem_locations (a b : α) : b ∈ S.locations a ↔ ∃ p, S.mv p a = b := by simp [locations,mem_motions]
lemma mv_mem_locations (a : α) (p : Motion) : S.mv p a ∈ S.locations a := (S.mem_locations ..).mpr ⟨p,rfl⟩
@[simp] lemma mem_own (a : α) : a ∈ S.locations a := (S.mem_locations ..).mpr ⟨1,S.mv_id a⟩
@[simp]
lemma carry_mem (a b : α) (p : Motion) : S.mv p b ∈ S.locations a ↔ b ∈ S.locations a := by
  rw [mem_locations,mem_locations]; refine ⟨?_,?_⟩
  · rintro ⟨q,h⟩; exact ⟨p⁻¹*q, by rw [mv_mul,h,← mv_mul,inv_mul_cancel,mv_id]⟩
  rintro ⟨q,rfl⟩; exact ⟨p*q,S.mv_mul ..⟩

/-- Read actual `±1` (once), or 0 if off orbit. -/
def weight (a b : α) : ℤ := match motions.find? (fun p => decide (S.mv p a = b)) with
  | some p => S.factor p a
  | none => 0
lemma weight_mv (a : α) (h : S.permits a) (p : Motion) :
    S.weight a (S.mv p a) = S.factor p a := by
  unfold weight; split
  next q he => rw [S.consistent a h q p (of_decide_eq_true (List.find?_some (p:=fun q => decide (S.mv q a = S.mv p a)) he))]
  next he =>
    simpa using (List.find?_eq_none.mp he) p (mem_motions p)
lemma weight_else {a b : α} (h : b ∉ S.locations a) : S.weight a b = 0 := by
  unfold weight
  split
  next p he => exact (h ((S.mem_locations ..).mpr ⟨p, of_decide_eq_true (List.find?_some (p:=fun q => decide (S.mv q a = b)) he)⟩)).elim
  rfl

def pieces (a : α) := (S.locations a).map (fun b => (b, S.weight a b))

/-- Choose least code. One doesn't even need a strictly tie-free code for the span
    calculation; for reproducing the MS lists we use keys implementing its order. -/
def issuing (e : List α) (code : α → ℕ) := e.filter fun a =>
  S.parity a && ((motions.all fun p => decide (code a ≤ code (S.mv p a))) && S.permits a)
lemma mem_issuing (e : List α) (code : α → ℕ) (a : α) : a ∈ S.issuing e code ↔
    a ∈ e ∧ S.permits a = true ∧ (∀ p, code a ≤ code (S.mv p a)) := by
  simp [issuing,mem_motions,permits_iff]; tauto

section
variable (K : Type*) [Field K]
noncomputable def column (a : α) : α → K := fun b => (S.weight a b : K)

lemma column_mem (a : α) (ha : S.permits a) : S.column K a ∈ S.invariant K := by
  rw [mem_invariant]
  constructor
  · intro b h
    by_cases u : b ∈ S.locations a
    · obtain ⟨p,rfl⟩ := (S.mem_locations ..).mp u
      rw [parity_mv]; exact ((S.permits_iff a).mp ha).1
    simp [column,S.weight_else u] at h
  · intro p b
    by_cases u : b ∈ S.locations a
    · obtain ⟨q,rfl⟩ := (S.mem_locations ..).mp u
      unfold column
      rw [← mv_mul, weight_mv _ _ ha, weight_mv _ _ ha,S.factor_mul]; simp
    simp [column,S.weight_else u,S.weight_else ((S.carry_mem a b p).not.mpr u)]
@[simp]
lemma column_at (a : α) (h : S.permits a) : S.column K a a = 1 := by
  unfold column
  have he : S.weight a a = 1 := by simpa using S.weight_mv a h 1
  simp [he]

variable {K} [CharZero K]
lemma permit_of_ne {x : α → K} (hx : x ∈ S.invariant K) (a : α) (h : x a ≠ 0) : S.permits a := by
  rcases (S.mem_invariant _).mp hx with ⟨h₁,h₂⟩
  rw [S.permits_iff]; refine ⟨h₁ a h, fun p e => ?_⟩
  have hz := h₂ p a; rw [e,zsmul_eq_mul] at hz
  have ht : ((S.factor p a : ℤ) : K) = 1 := mul_right_cancel₀ h (hz.symm.trans (one_mul _).symm)
  apply Units.ext; change (S.factor p a : ℤ) = 1; exact_mod_cast ht
omit [DecidableEq α] in
@[simp]
lemma carried_zero {x : α → K} (hx : x ∈ S.invariant K) (p : Motion) (a : α) : x (S.mv p a) = 0 ↔ x a = 0 := by
  rw [((S.mem_invariant _).mp hx).2]
  simp

lemma exhaust (e : List α) (covers : ∀ i, i ∈ e) (code : α → ℕ) (x : α → K)
    (hx : x ∈ S.invariant K) (b : α) (h : x b ≠ 0) :
    ∃ a ∈ S.issuing e code, ∃ p, b = S.mv p a := by
  obtain ⟨p,hp⟩ := Finite.exists_min (fun p : Motion => code (S.mv p b))
  refine ⟨S.mv p b, (S.mem_issuing ..).mpr ⟨covers _,S.permit_of_ne hx _
    (by rw [ne_eq, S.carried_zero hx]; exact h), fun q => S.mv_mul q p b ▸ hp (q*p)⟩,
    p⁻¹, by rw [← mv_mul,inv_mul_cancel,mv_id]⟩

variable (K)
lemma span_columns (e : List α) (covers : ∀ i, i ∈ e) (code : α → ℕ) :
    S.invariant K = Submodule.span K (S.column K '' {a | a ∈ S.issuing e code}) := by
  apply le_antisymm _ (Submodule.span_le.mpr ?_)
  rotate_left
  · rintro _ ⟨a,he,rfl⟩; exact S.column_mem K a ((S.mem_issuing ..).mp he).2.1
  -- kill a nonzero orbit, recurse on number of nonzero entries
  classical
  let support (x : α → K) := e.toFinset.filter (fun i => x i ≠ 0)
  let R := Submodule.span K (S.column K '' {a | a ∈ S.issuing e code})
  suffices H : ∀ n : ℕ, ∀ x ∈ S.invariant K, (support x).card = n → x ∈ R by
    exact fun x h => H (support x).card x h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx hn
    by_cases h : x = 0
    · rw [h]; exact R.zero_mem
    obtain ⟨b,hb⟩ : ∃ b : α, x b ≠ 0 := Function.ne_iff.mp h
    obtain ⟨a,ha,p,hp⟩ := S.exhaust e covers code x hx b hb
    have ha' := ((S.mem_issuing ..).mp ha).2.1
    let y := x a • S.column K a
    have hy : y ∈ R := R.smul_mem _ (Submodule.subset_span ⟨a,ha,rfl⟩)
    have hz : x-y ∈ S.invariant K := (S.invariant K).sub_mem hx ((S.invariant K).smul_mem _ (S.column_mem K a ha'))
    have he : (support (x-y)).card < n := by
      rw [← hn]; apply card_lt_card
      have m i (x : α → K) : i ∈ support x ↔ x i ≠ 0 := by simp [support,covers]
      have ht : x a ≠ 0 := ((S.carried_zero hx p a).not.mp (hp ▸ hb : x (S.mv p a) ≠ 0))
      have ht' : (x-y) a = 0 := by simp [y,S.column_at K a ha']
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun H => ((m a (x-y)).mp (H.symm ▸ (m a x).mpr ht)) ht'⟩
      intro i hi
      apply (m i x).mpr
      by_cases u : i ∈ S.locations a
      · obtain ⟨p',rfl⟩ := (S.mem_locations ..).mp u; exact (S.carried_zero hx p' a).not.mpr ht
      have hy' := (m i (x-y)).mp hi
      simpa [y,column,weight_else S u] using hy'
    simpa only [sub_add_cancel] using R.add_mem (ih _ he (x-y) hz rfl) hy
end
end SatinStress.U1.Slot
