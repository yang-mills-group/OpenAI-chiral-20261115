import GaugeFieldConstruction.Vouchers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Pivot test: static input is each separator (positive pivots) or
Gaussian-integer linear combination of existing pivots (negative pivots).
The two reports are only accepted with a proof by this validator. -/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers
open Finset Function Complex Cauchy
open scoped BigOperators
variable {α β : Type*}
namespace Bill
variable [DecidableEq α]

/-- Combine like terms while evaluating. -/
def fuse (x : α) (c : Credit) : Bill α → Bill α
  | [] => flash x c
  | (y,d)::l => if x=y then flash x (c+d) ++ l else (y,d)::fuse x c l
lemma strengthen (x : α) (c) (l : Bill α) : total (fuse x c l)=c.money • ket x+ total l := by
  induction l with
  | nil => simp only [fuse,take_flash,total,add_zero]
  | cons i l h=> unfold fuse; split
                 · subst_eqs
                   rw [total_append,take_flash,total,Credit.plus,add_smul,add_assoc]
                 rw [total,h,add_left_comm,total]

def norm : Bill α → Bill α | []=> [] | i::l=>fuse i.1 i.2 (norm l)
lemma same (l : Bill α) : total (norm l)=total l := by
  induction l with
  | nil => rfl
  | cons i l h=> rw [norm,strengthen,h,total]

def cash (x : α) : Bill α → Credit
  | [] => 0
  | (y,d)::v => if x=y then d+cash x v else cash x v
lemma spendable (x : α) (l : Bill α) : (cash x l).money=total l x := by
  induction l with
  | nil => exact Credit.zero_c
  | cons i l h =>
    cases i; unfold cash; split
    · subst_eqs; simp [total, h, ket]
    next e => simp [total,h,ket,Finsupp.single_apply, Ne.symm e]

/-- dual test -/
def query (l : Bill α) : Bill α → Credit
  | [] => 0
  | (x,c)::v=>c*cash x l+query l v
noncomputable def dual : Bill α → J α →ₗ[ℂ] ℂ
  | [] => 0
  | (x,c)::v => c.money • Finsupp.lapply x + dual v
lemma price (l p : Bill α) : (query l p).money=dual p (total l) := by
  induction p with
  | nil => exact Credit.zero_c
  | cons i p h=> cases i; rw [dual,query,Credit.plus,Credit.times,h,spendable]; rfl

def pile : List Credit → List (Bill α) → Bill α
  | a::u,b::t => spend a b ++ pile u t
  | _,_ => []

omit [DecidableEq α] in
lemma piled (l : List (Bill α)) (d : List Credit) (H : Submodule ℂ (J α))
    (h : ∀ i∈l,total i∈H) : total (pile d l) ∈ H := by
  induction d generalizing l with
  | nil => exact Submodule.zero_mem _
  | cons a d ih=>
    cases l with
    | nil => exact H.zero_mem
    | cons b l=> rw [pile,total_append,cost]; exact H.add_mem (H.smul_mem _ (h _ (by simp)))
                        (ih l (fun i hi => h _ (by simp [hi])))
end Bill
open Bill
inductive Stub (α : Type*) where
  | success : Bill α → Stub α
  | decline : Credit → List Credit → Stub α

variable [DecidableEq α]

open Stub
/-- list of accepted (reverse order), new list, pivot bits, certificate stubs -/
def verify (Y : List (Bill α)) (L : List (Bill α)) (b : List Bool) (h : List (Stub α)) : Bool :=
  match L,b,h with
  | x::l,true::t,success k::c =>
    !(decide (query x k=0)) && (Y.all fun i => decide (query i k=0)) && verify (x::Y) l t c
  | x::l,false::t,decline d j::c => !(decide (d=0)) &&
    (Bill.norm (spend d x ++ pile j Y)).isEmpty && verify Y l t c
  | [],[],[]=>true
  | _,_,_=>false

open Submodule
theorem spends (Y : List (Bill α)) (L b h) (u : verify Y L b h = true) : scan (L.map total) b (line (Y.map total)) := by
  induction L generalizing Y b h with
  | nil => cases b <;> cases h <;> simp_all [verify,scan]
  | cons x L ih=>
    match b,h with
    | true::t,success k::c =>
      simp only [verify,Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true,decide_eq_false_iff_not] at u
      have ht : line (Y.map total) ≤ LinearMap.ker (Bill.dual k) := span_le.mpr (by
        intro i hi
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
        change (Bill.dual k) (total j)=0; rw [← price]; rw [show query j k=0 from of_decide_eq_true (List.all_eq_true.mp u.1.2 j hj)]; simp)
      refine ⟨fun p => Credit.nonzero _ |>.mpr u.1.1 <| (price ..).trans (ht p),?_⟩ -- tweak
      have he : line ((x::Y).map total) = line (Y.map total) ⊔ span ℂ {total x} := by
        unfold line; rw [← span_union]; congr; ext i
        change i∈List.map _ _ ↔ i∈(_ : Set (J α)); simp [or_comm]
      rw [← he]; exact ih _ t c u.2
    | false::t,decline d j::c =>
      simp only [verify,Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true,decide_eq_false_iff_not] at u
      have hz : total (spend d x ++ pile j Y)=0 := by rw [← Bill.same, List.isEmpty_iff.mp u.1.2]; rfl
      rw [total_append,Bill.cost] at hz
      have he : total x∈line (Y.map total) := by
        have hp := piled Y j (line (Y.map total)) (fun i hi => subset_span (show _∈(Y.map total) from List.mem_map.mpr ⟨i,hi,rfl⟩))
        have hg := (line (Y.map total)).smul_mem d.money⁻¹ ((line (Y.map total)).neg_mem hp)
        rwa [← eq_neg_of_add_eq_zero_left hz, inv_smul_smul₀ ((Credit.nonzero _).mpr u.1.1)] at hg
      refine ⟨he,?_⟩
      rw [sup_eq_left.mpr ((span_singleton_le_iff_mem ..).mpr he)]
      exact ih _ t c u.2
    | [],c => simp [verify] at u
    | true::t,decline d j::c => simp [verify] at u
    | false::t,success k::c => simp [verify] at u
    | true::t, [] => simp [verify] at u
    | false::t, [] => simp [verify] at u

theorem billed (L : List (Bill α)) (b h) (u : verify [] (L.map Bill.norm) b h=true) : Scan0 (L.map total) b := by
  have hp := spends _ _ _ _ u
  unfold Scan0; simpa [Function.comp_def,line,Bill.same] using hp

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open Module
lemma counts (l : List V) (b : List Bool) (H : Submodule ℂ V) [FiniteDimensional ℂ H] (h : scan l b H) :
    finrank ℂ (H ⊔ line l : Submodule ℂ V) = finrank ℂ H + b.count true := by
  induction l generalizing H b with
  | nil =>
    cases b
    · unfold line; rw [show {x | x ∈ ([]:List V)}=∅ by simp,span_empty,sup_bot_eq]; simp
    simp [scan] at h
  | cons x l ih =>
    have he : line (x::l) = line l ⊔ span ℂ {x} := by
      rw [line,line,← span_union]; congr; ext p
      change p∈x::l ↔ p∈(_ : Set V); simp [or_comm]
    cases b with
    | nil => exact False.elim h
    | cons t b=>
      rw [he,sup_comm (line l),← sup_assoc]
      cases t <;> rw [ih _ _ h.2]
      · rw [sup_eq_left.mpr ((span_singleton_le_iff_mem ..).mpr h.1)]
        simp
      have hy : x ≠ 0 := fun u => h.1 (u ▸ zero_mem _)
      have hm := finrank_sup_add_finrank_inf_eq H (span ℂ {x})
      rw [Disjoint.eq_bot (Submodule.disjoint_span_singleton_of_notMem h.1),finrank_bot,Nat.add_zero,finrank_span_singleton hy] at hm
      rw [hm]; simp [add_comm,add_left_comm,add_assoc]
end YM.GaugeFieldConstruction.Vouchers
