import SatinStress.U1.Derivative
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod

namespace SatinStress.U1
open Derivative
open Raw (pick hull denote PivotList Earlier)
open Function (Injective)
open Submodule (span)
open Module (finrank)
open Class (TT W V)
namespace Raw
variable (K : Type*) [Field K] [Algebra K ℂ]
lemma pivot_suffices {a : Type} {x : List (Raw a)} {j : List ℕ} (H : Earlier K j 1 [] x) :
    hull K x = hull K (pick j 1 x) := by simpa using H.hull K
lemma moved {a b : Type} (x : List (Raw a)) (f : Raw a → Raw b) (F : Grid a →ₗ[K] Grid b)
    (e : ∀ i, denote (f i) = F (denote i)) : (hull K x).map F = hull K (x.map f) := by
  unfold hull
  rw [Submodule.map_span]
  congr 1
  ext t
  simp only [Set.mem_image, Set.mem_setOf_eq,List.map_map, List.mem_map, Function.comp_apply,e]
  grind
lemma merge {a : Type} (x y : List (Raw a)) : hull K (x++y) = hull K x ⊔ hull K y := by
  unfold hull
  rw [← Submodule.span_union]; congr 1; ext; simp
end Raw

namespace Sequence

variable (K : Type*) [Field K] [Algebra K ℂ] {pol m o a : Type}
  (C : Class pol m) (H : Class pol a) (s : Freq) [Fintype m] [Fintype a]
noncomputable section

instance (X : Schedule o) [Fintype o] : FiniteDimensional K (C.image X K) := by
  unfold Class.image; exact Module.Finite.map _ _

-- ranks of these use one subtype domain, not restricting the codomain yet.
abbrev tr := (traceT K).domRestrict (C.image TT K)
abbrev D := (divT K s).domRestrict (C.image TT K)
abbrev up := (gradT K s).domRestrict (C.image TT K)

/-- (93). **V then W, minus sign**. Domain notation agrees with equation (93); pivots tested below
    on the list order W then V and with both positive signs (MS supplementary convention). -/
def difference : ((H.image V K) × (H.image W K)) →ₗ[K] Grid (DR pol) :=
  ((divV K s).domRestrict (H.image V K)).coprod (-((gradW K s).domRestrict (H.image W K)))
lemma difference_apply (x : _ × _) : -- give type?
    difference K H s x = divV K s x.1.val - gradW K s x.2.val := by
  simp [difference, sub_eq_add_neg]

/-- Once both maps shown to land in our invariant image spaces. -/
structure Lands : Prop where
  vw : LinearMap.range (up K C s) ≤ H.image V K
  ww : LinearMap.range (D K C s) ≤ H.image W K

def previous (h : Lands K C H s) : (C.image TT K) →ₗ[K] (H.image V K) × (H.image W K) :=
  ((up K C s).codRestrict _ (fun i => h.vw ⟨i,rfl⟩)).prod ((D K C s).codRestrict _ (fun i => h.ww ⟨i,rfl⟩))
@[simp] lemma prev_one (h : Lands K C H s) (t : C.image TT K) : (previous K C H s h t).1.val = gradT K s t.val := rfl
@[simp] lemma prev_two (h : Lands K C H s) (t : C.image TT K) : (previous K C H s h t).2.val = divT K s t.val := rfl
lemma prev_inj (h : Lands K C H s) (h0 : (s 0).den ≠ 0) : Injective (previous K C H s h) :=
  fun _ _ e => Subtype.ext (monoT K s h0 pol
    (congr_arg (fun x : (H.image V K) × (H.image W K) => x.1.val) e))
lemma next_zero (h : Lands K C H s) (t : C.image TT K) : difference K H s (previous K C H s h t) = 0 := by
  rw [difference_apply,prev_one,prev_two,closed,sub_self]

/-- Any block (or put direct sum later), rank criterion for the free (94). -/
lemma exact_criterion (h : Lands K C H s) (h0 : (s 0).den ≠ 0)
    (rank : finrank K (LinearMap.range (difference K H s)) + finrank K (C.image TT K) = finrank K (H.image V K) + finrank K (H.image W K)) :
    LinearMap.range (previous K C H s h) = LinearMap.ker (difference K H s) := by
  have e := LinearMap.finrank_range_add_finrank_ker (difference K H s)
  rw [Module.finrank_prod] at e
  refine Submodule.eq_of_le_of_finrank_le ?_ ?_
  · rintro x ⟨t,rfl⟩; exact LinearMap.mem_ker.mpr (next_zero K C H s h t)
  · rw [LinearMap.finrank_range_of_inj (prev_inj K C H s h h0)]
    omega

end

section Construct
variable [CharZero K] [DecidableEq m] [DecidableEq a]
  (jT jW jV jTrace jD j93 : List ℕ)

/-- Input independent arithmetic pieces, *on the Class labels and momentum multiplier*
    (no choice of test arrays here). Includes the exact pivot list proofs in the specified order.
    And `landing` hypotheses will be proved by giving upper dependences (again at exactly
    the same columns), separately. -/
structure Tables : Prop where
  matT : PivotList K (C.bake TT) jT
  matW : PivotList K (H.bake W) jW
  matV : PivotList K (H.bake V) jV
  tr : PivotList K ((pick jT 1 (C.bake TT)).map rawTrace) jTrace
  div : PivotList K ((pick jT 1 (C.bake TT)).map (rawDiv s)) jD
  comparison : PivotList K (((pick jW 1 (H.bake W)).map (rawW s)) ++
                  (pick jV 1 (H.bake V)).map (rawV s)) j93
  landV : hull K ((pick jV 1 (H.bake V)) ++ (pick jT 1 (C.bake TT)).map (rawT s)) =
    hull K (pick jV 1 (H.bake V))
  landW : hull K ((pick jW 1 (H.bake W)) ++ (pick jT 1 (C.bake TT)).map (rawDiv s)) =
    hull K (pick jW 1 (H.bake W))

variable {K C H s jT jW jV jTrace jD j93} (v : Tables K C H s jT jW jV jTrace jD j93)
include v
omit [Fintype a] in
lemma Tables.costT : C.image TT K = hull K (pick jT 1 (C.bake TT)) :=
  (C.currency K _).trans (v.matT.same K)
omit [Fintype m] in
lemma Tables.costW : H.image W K = hull K (pick jW 1 (H.bake W)) :=
  (H.currency K _).trans (v.matW.same K)
omit [Fintype m] in
lemma Tables.costV : H.image V K = hull K (pick jV 1 (H.bake V)) :=
  (H.currency K _).trans (v.matV.same K)
omit [Fintype a] in
lemma Tables.outT : finrank K (C.image TT K) = jT.length := by
  rw [C.currency]; exact v.matT.rank K
omit [Fintype m] in
lemma Tables.outW : finrank K (H.image W K) = jW.length := by
  rw [H.currency]; exact v.matW.rank K
omit [Fintype m] in
lemma Tables.outV : finrank K (H.image V K) = jV.length := by
  rw [H.currency]; exact v.matV.rank K
omit [Fintype a] in
lemma Tables.outTrace : finrank K (LinearMap.range (Sequence.tr K C)) = jTrace.length := by
  rw [Sequence.tr,LinearMap.range_domRestrict, v.costT, Raw.moved K _ _ _ (luTrace K)]; exact v.tr.rank K
omit [Fintype a] in
lemma Tables.outD : finrank K (LinearMap.range (D K C s)) = jD.length := by
  rw [D,LinearMap.range_domRestrict, v.costT, Raw.moved K _ _ _ (luDiv K s)]; exact v.div.rank K
omit [Fintype m] in
lemma Tables.out93 : finrank K (LinearMap.range (difference K H s)) = j93.length := by
  rw [difference,LinearMap.range_coprod,LinearMap.range_neg,
    LinearMap.range_domRestrict,LinearMap.range_domRestrict,v.costW,v.costV,sup_comm,
    Raw.moved K _ _ _ (luGW K s),Raw.moved K _ _ _ (luV K s), ← Raw.merge]
  exact v.comparison.rank K
lemma Tables.lands : Lands K C H s := by
  constructor
  · rw [up,LinearMap.range_domRestrict,v.costT,v.costV,Raw.moved K _ _ _ (luGT K s)]
    exact sup_eq_left.mp ( (Raw.merge ..).symm.trans v.landV)
  · rw [D,LinearMap.range_domRestrict,v.costT,v.costW,Raw.moved K _ _ _ (luDiv K s)]
    exact sup_eq_left.mp ( (Raw.merge ..).symm.trans v.landW)
lemma Tables.exact (h0 : (s 0).den ≠ 0) (e : j93.length + jT.length = jV.length + jW.length) :
    LinearMap.range (previous K C H s v.lands) = LinearMap.ker (difference K H s) := by
  apply exact_criterion _ _ _ _ v.lands h0
  rwa [v.out93,v.outW,v.outT,v.outV]
end Construct
end Sequence
end SatinStress.U1
