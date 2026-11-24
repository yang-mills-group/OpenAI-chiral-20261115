import YM.CF.Lattice.Local
import YM.CF.Fock.Salary

/-! Union-hit calculus, pays volume in native lattice units. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open Finset

structure Field (Y : Type*) where
  span : Y→Y→ℕ
  reflex (x : Y) : span x x=0
  sym (x y : Y) : span x y=span y x
  tri (x y z : Y) : span x z≤span x y+span y z
variable {Y : Type*} [DecidableEq Y]

inductive Grove (B : Field Y) : Finset Y → Prop where
  | single (x : Y) : Grove B {x}
  | join {S : Finset Y} : ∀ {x y : Y}, Grove B S→ y∈S → B.span x y≤1 → Grove B (insert x S)

variable {B : Field Y} {S T : Finset Y} {x y : Y}
lemma Grove.lim (h : Grove B S) : ∀ x∈S, ∀ y∈S, B.span x y < S.card := by
  induction h with
  | single x => intro u hu v hv; rw [mem_singleton.mp hu,mem_singleton.mp hv,B.reflex]; simp
  | @join S x y _ e g ih =>
    by_cases l : x∈S
    · rw [insert_eq_of_mem l]; exact ih
    intro a h b k; rw [card_insert_of_notMem l]
    have hn i (hi:i∈S) : B.span x i < S.card+1 := by
      have he := B.tri x y i; have ht := ih y e i hi; omega
    rcases mem_insert.mp h with f|f <;> rcases mem_insert.mp k with m|m
    · subst b a; rw [B.reflex]; omega
    · rw [f]; exact hn _ m
    · rw [m,B.sym]; exact hn _ f
    exact (ih a f b m).trans (by omega)
-- use paths for unions
abbrev Origin (B : Field Y) (S : Finset Y) (x y : Y) := Relation.ReflTransGen (fun a b:Y=>a∈S ∧ b∈S ∧ B.span a b≤1) x y
lemma orig_flip (h : Origin B S x y) : Origin B S y x := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact .head ⟨e.2.1,e.1,(B.sym ..).trans_le e.2.2⟩ ih
lemma orig_sub (h : Origin B S x y) (g : S ⊆ T) : Origin B T x y := by
  induction h with
  | refl => exact .refl
  | tail _ t ih => exact .tail ih ⟨g t.1,g t.2.1,t.2.2⟩
lemma rooted (h : Grove B S) : ∀ x∈S, ∀ y∈S, Origin B S x y := by
  induction h with
  | single x => intro u hu v hv; rw [mem_singleton.mp hu,mem_singleton.mp hv]
  | @join S x y _ e g ih =>
    have hl v (hv:v∈S) : Origin B (insert x S) x v := Relation.ReflTransGen.head ⟨mem_insert_self ..,mem_insert_of_mem e,g⟩ (orig_sub (ih y e v hv) (subset_insert _ _)) -- tune
    intro a h b k
    rcases mem_insert.mp h with f|f <;> rcases mem_insert.mp k with m|m
    · subst b a; exact .refl
    · rw [f]; exact hl _ m
    · rw [m]; exact orig_flip (hl _ f)
    exact orig_sub (ih a f b m) (subset_insert _ _)
lemma trunk (u : x∈S) (h : ∀ y∈S, Origin B S x y) : Grove B S := by
  suffices he : ∀ A : Finset Y, A⊆S → Grove B A → x∈A → Grove B S from he {x} (singleton_subset_iff.mpr u) (.single _) (mem_singleton.mpr rfl)
  intro A ht g k
  generalize hN : S.card-A.card = N
  induction N using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases e : S ⊆ A
    · rw [Subset.antisymm e ht]; exact g
    obtain ⟨i,f,p⟩ := not_subset.mp e
    have hd : ∀ y, Origin B S x y → y∉A → ∃ v∈A, ∃ t∈S, t∉A ∧ B.span t v≤1 := by
      intro y l
      induction l with
      | refl => tauto
      | @tail z w he hq H => intro j; by_cases hy:z∈A; exact ⟨z,hy,w,hq.2.1,j,(B.sym ..).trans_le hq.2.2⟩; exact H hy
    obtain ⟨v,l,t,f,p,q⟩ := hd _ (h i f) p
    have he : insert t A ⊆ S := insert_subset f ht
    apply ih _ _ _ he (.join g l q) (mem_insert_of_mem k) rfl
    have ha := card_le_card he; rw [card_insert_of_notMem p] at *; omega
lemma Grove.unite (h : Grove B S) (g : Grove B T) (k : x∈S) (l : x∈T) : Grove B (S∪T) := by
  apply trunk (B:=B) (mem_union_left T k); intro y hy
  rcases mem_union.mp hy with f|f
  · exact orig_sub (rooted h x k y f) subset_union_left
  exact orig_sub (rooted g x l y f) subset_union_right

variable [Fintype Y]
def bay (B : Field Y) (x : Y) (n : ℕ) := univ.filter fun y=> B.span x y ≤ n
@[simp] lemma bay_mem (n : ℕ) : y ∈ bay B x n ↔ B.span x y≤n := by simp [bay]
lemma trunk_bay (B : Field Y) (h : ∀ (x y : Y), Origin B (bay B x (B.span x y)) x y) (x : Y) (n : ℕ) : Grove B (bay B x n) := by
  apply trunk (B:=B) (show x∈bay B x n from bay_mem n|>.mpr (by rw [B.reflex]; omega)); intro y hy
  apply orig_sub (h x y); intro i hi; rw [bay_mem] at *; omega
lemma Grove.basin (h : Grove B S) (u : x∈S) : S ⊆ bay B x S.card := by intro y hy; rw [bay_mem]; exact (h.lim x u y hy).le
end YM.CF.Branch
