import SatinStress.U1.Chart
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.RingHom
/-!
# Certifying pivots

Separate lower & upper rank witnesses. Upper: dependence on **earlier selected
columns**. Lower: explicit test rows and inverse (up to a nonzero scale) on
sampled polynomial coefficients. We don't need assumptions on nonsingularity of
pivots not validated in Lean.
-/

namespace SatinStress.U1
open Radix Finset Submodule
open scoped BigOperators

namespace Raw
variable {q : Type}

-- helper operations for column checks. no mathematical structure on Expr.
def plus (x y : Raw q) : Raw q := fun i => x i + y i
def times (n : ℤ) (x : Raw q) : Raw q := fun i => Expr.conZ n * x i
def zero : Raw q := fun _ => 0
@[simp] lemma denote_plus (x y : Raw q) : (x.plus y).denote = x.denote + y.denote := by ext1 i; simp [plus,denote]
@[simp] lemma denote_times (n : ℤ) (x : Raw q) : (x.times n).denote = n • x.denote := by ext1 i; simp [times,denote]
@[simp] lemma denote_zero : Raw.denote (zero (q:=q)) = 0 := by ext1 i; simp [zero,denote]

def relation (v : List ((Raw q) × ℤ)) : Raw q := v.foldr (fun p y => (times p.2 p.1).plus y) zero
@[simp] lemma relation_step (v : List ((Raw q) × ℤ)) (f : Raw q) (i : ℤ) :
    relation ((f,i)::v) = (times i f).plus (relation v) := rfl
@[simp] lemma relation_nil : relation (q:=q) [] = zero := rfl
lemma spends {x : Raw q} {e : List q} (h : ∀ i, i ∈ e) (r : e.all (fun i => (x i).spends) = true) : x.denote = 0 :=
  funext fun i => (x i).spend_zero (List.all_eq_true.mp r i (h i))
lemma of_rel {d : Raw q} {w : List ((Raw q) × ℤ)} {i : ℤ} (h : (relation ((d,i)::w)).denote = 0) :
    i • d.denote = -(relation w).denote := eq_neg_of_add_eq_zero_left (by simpa only [relation_step,denote_plus,denote_times] using h)

-- could use basis.index but storing exact pivot lists relative to unprocessed enumeration convenient
noncomputable def hull (K : Type*) [Field K] [Algebra K ℂ] (v : List (Raw q)) :=
  span K {x | x ∈ v.map denote}
@[simp] theorem hull_nil (K : Type*) [Field K] [Algebra K ℂ] : hull (q:=q) K [] = ⊥ := by simp [hull]

section Upper
variable (K : Type*) [Field K] [Algebra K ℂ]
lemma entry (d : Raw q) (v : List (Raw q)) (h : d ∈ v) : d.denote ∈ hull K v :=
  subset_span (List.mem_map_of_mem h)

lemma subs {v u : List (Raw q)} (h : ∀ x ∈ v, x.denote ∈ hull K u) : hull K v ≤ hull K u := by
  apply span_le.mpr; intro i hi
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (show i ∈ v.map denote from hi); exact h x hx
-- avoid coercion x.denote on implicit unknown x binder? compile

lemma perm {v u : List (Raw q)} (h : ∀ x, x ∈ v ↔ x ∈ u) : hull K v = hull K u :=
  le_antisymm (subs K (fun x hx => entry K _ _ ((h x).mp hx))) (subs K (fun x hx => entry K _ _ ((h x).mpr hx)))

lemma hull_cons (v : List (Raw q)) (d : Raw q) : hull K (d::v) = K ∙ d.denote ⊔ hull K v := by
  simp only [hull, ← span_union]; congr 1
  ext i; simp only [List.map_cons, Set.mem_setOf_eq, List.mem_cons, Set.mem_union, Set.mem_singleton_iff]
lemma rel_mem {w : List ((Raw q) × ℤ)} {v : List (Raw q)} (he : ∀ u ∈ w, u.1 ∈ v) :
    (relation w).denote ∈ hull K v := by
  induction w with
  | nil => simp
  | cons a as ih =>
    rw [show a::as = (a.1,a.2)::as from rfl,relation_step,denote_plus,denote_times]
    exact (hull K v).add_mem (zsmul_mem (entry K _ _ (he a (by simp))) _) (ih (fun i h => he i (by simp [h])))
lemma kill [CharZero K] (d : Raw q) {v : List (Raw q)} (i : ℤ) (w : List ((Raw q) × ℤ)) (t : i ≠ 0)
    (he : ∀ u ∈ w, u.1 ∈ v) (h : i • d.denote = -(relation w).denote) :
    d.denote ∈ hull K v := by
  apply (hull K v).smul_mem_iff (show (i : K) ≠ 0 by exact_mod_cast t) |>.mp
  rw [Int.cast_smul_eq_zsmul K i d.denote,h]
  exact (hull K v).neg_mem (rel_mem K he)

-- use actual listed indices (1-indexed)
def pick (j : List ℕ) (start : ℕ) (v : List (Raw q)) : List (Raw q) := match v with
  | [] => []
  | d::v => if start ∈ j then d :: pick j (start+1) v else pick j (start+1) v

inductive Earlier (j : List ℕ) : ℕ → List (Raw q) → List (Raw q) → Prop where
  | nil (k v) : Earlier j k v []
  | piv {k v d x} (hk : k ∈ j) (next : Earlier j (k+1) (d::v) x) : Earlier j k v (d::x)
  | dep {k v d x} (hk : k ∉ j) (existsCombination : d.denote ∈ hull K v) (next : Earlier j (k+1) v x) : Earlier j k v (d::x)

lemma Earlier.hull {x : List (Raw q)} {start : ℕ} {j : List ℕ} {y : List (Raw q)}
    (H : Earlier K j start y x) : hull K (y ++ x) = hull K (y ++ pick j start x) := by
  induction H with
  | nil => rfl
  | @piv k v d x hk _ ih =>
    rw [pick, if_pos hk, perm K (v:=v ++ d::x) (u:=d::v ++ x) (by simp; tauto),ih]
    exact perm K (by simp; tauto)
  | @dep k v d x hk u _ ih =>
    rw [pick,if_neg hk,perm K (v:=v ++ d::x) (u:=d::(v ++ x)) (by simp; tauto), hull_cons, sup_eq_right.mpr, ih]
    exact (span_singleton_le_iff_mem ..).mpr (subs K (v:=v) (u:=v++x) (fun a ha => entry K _ _ (by simp [ha])) u)
-- Ensure omitted columns depend on earlier pivots only; assert LI of pivot subsequence.
-- Thus a full certificate in the specified order, independent even of whether our
-- order agrees with Python's lex convention (it is intended to).
structure PivotList (v : List (Raw q)) (j : List ℕ) : Prop where
  ordered : j.Pairwise (· < ·)
  size : (pick j 1 v).length = j.length
  upper : Earlier K j 1 [] v
  lower : LinearIndependent K (fun i : Fin (pick j 1 v).length => denote ((pick j 1 v).get i))
lemma PivotList.same {v : List (Raw q)} {j : List ℕ} (H : PivotList K v j) : hull K v = hull K (pick j 1 v) :=
  by simpa using Earlier.hull K H.upper
lemma PivotList.rank {v : List (Raw q)} {j : List ℕ} (H : PivotList K v j) : Module.finrank K (hull K v) = j.length := by
  let x := pick j 1 v
  rw [H.same]
  have he : hull K x = span K (Set.range (fun i : Fin x.length => denote (x.get i))) := by
    unfold hull; congr 1; ext b
    refine ⟨?_,?_⟩
    · intro hb; obtain ⟨d,h,rfl⟩ := List.mem_map.mp (show b ∈ x.map denote from hb)
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp h; exact ⟨i,rfl⟩
    rintro ⟨i,rfl⟩; exact List.mem_map.mpr ⟨_,List.get_mem x i,rfl⟩
  change Module.finrank K (hull K x) = _
  rw [he, finrank_span_eq_card H.lower, Fintype.card_fin, show x.length = j.length from H.size]
end Upper

section Lower
abbrev Probe (q : Type) := q × ℕ
/-- table of projected readings -/
def ear (p : Probe q) (x : Raw q) := Radix.Tape.look p.2 (x p.1).sparse
def sample (rows : List (Probe q)) (v : List (Raw q)) : List (List GI) :=
  v.map (fun x => rows.map fun p => ear p x) -- outer list over *columns*

def charge : List GI → List GI → GI
  | k::ks, r::rs => k*r + charge ks rs
  | _, _ => 0

variable (K : Type*) [Field K] [Algebra K ℂ]
-- Linear combination of probes evaluated into C, coefficients in GI (C-linear)
noncomputable def read : List GI → List (Probe q) → (Grid q →ₗ[K] ℂ)
  | k::ks, r::rs =>
    ((k.c • ((test r.2).comp (LinearMap.proj r.1) : Grid q →ₗ[ℂ] ℂ)).restrictScalars K) + read ks rs -- recursive?
  | _, _ => 0

lemma read_eq (k : List GI) (rows : List (Probe q)) (v : Raw q) :
    read K k rows v.denote = GI.c (charge k (rows.map (fun p => ear p v))) := by
  induction k generalizing rows with
  | nil => cases rows <;> simp [read, charge]
  | cons a as ih =>
    cases rows with
    | nil => simp [read,charge]
    | cons b bs =>
      rw [read,LinearMap.add_apply,ih]; change a.c * test b.2 (v b.1).den + _ = _
      rw [Expr.micro]
      simp only [charge,List.map_cons,GI.c_add,GI.c_mul,ear]
      -- simp order

/-- Every diagonal nonzero, all off-diagonal exactly zero. `dual` gives
    integer (GI) row combinations. Validate using a table first for kernel cost.
    Use option defaulting for the matrix test: a missing dual returns [] and
    therefore couldn't pass a diagonal test. Only ever use this for lower ranks. -/
lemma verified (rows : List (Probe q)) (v : List (Raw q)) {M : List (List GI)}
    (h : sample rows v = M) (dual : List (List GI))
    (hq : ∀ i j : Fin v.length,
      charge (dual[i.val]?.getD []) ((M[j.val]?).getD []) = 0 ↔ i ≠ j) :
    LinearIndependent K (fun i : Fin v.length => denote (v.get i)) := by
  subst M
  rw [Fintype.linearIndependent_iff]; intro u hu i
  let L := read K (dual[i.val]?.getD []) rows
  have he (j : Fin v.length) : L ((v.get j).denote) = 0 ↔ i ≠ j := by
    rw [show L = _ from rfl,read_eq,← GI.c_zero,GI.c_inj]
    simpa [sample,j.isLt] using hq i j
  have hy : L (∑ j, u j • (v.get j).denote) = 0 := hu ▸ map_zero _
  simp_rw [map_sum, map_smul] at hy
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [(he j).mpr (Ne.symm hj),smul_zero]) (by simp)] at hy
  exact (smul_eq_zero_iff_left (show L ((v.get i).denote) ≠ 0 from fun h => (he i).mp h rfl)).mp hy
end Lower
end Raw
end SatinStress.U1

namespace SatinStress.U1.Raw
open Radix
theorem join_readings {q : Type} (rows : List (Probe q)) {u v : List (Raw q)}
    {A B : List (List GI)} (h : sample rows u = A) (t : sample rows v = B) :
    sample rows (u++v) = A ++ B := by subst A; subst B; simp [sample]
end SatinStress.U1.Raw
