import SatinStress.U1.Certificate.Summary
/-!
# The U1 finite rank table

**Scope** here: the complex polynomial tests specified in the rank calculation, on
the stated g/f/x raw sectors with precisely the `Slot` transformations, including
the determinant bit. The rank bounds apply both over K=ℝ (real span of these labels)
and K=ℂ. A derivative in this theorem is the U1 test on the *momentum polynomials*.

These are not ranks of any invented full hierarchy. Application to the hierarchy in
the manuscript requires identities from (62), R1--4 (including identification of
flavor/color slots, and the identification of the free reflection norm null relations
with the on-shell and chart-polynomial tests). And there's no *comparison hypothesis*
for the interacting trajectory in the certificate checks; that would be another step,
not concluded from these ranks.

Below the conclusion exhibits `finrank`, exactness, injectivity even of each one-
component (and second) derivative of T, and also the actual pivot lists, on the
`Class.bake` columns, so neither `python` verification nor even choosing those
columns as input arrays has to be trusted. For indices of T,W,V, cf `Class` and
`Schedule`. Lists use 1-index, and the derivative pivots use the *reduced* lists
just as in the submission (comparison (93) checks W then V, + sign for purposes
of pivot indices only). In the rank theorem itself on (93) the sign is negative,
and domain order V then W.
-/
namespace SatinStress.U1
open Class
open Radix Certificate Sequence Derivative
open Module (finrank)
open Function (Injective)
open Raw (pick hull)

lemma nonzero_of_seen (x : Expr) (i : ℕ) (h : Tape.look i x.sparse ≠ 0) : x.den ≠ 0 :=
  fun he => h ((x.row_zero i).mp (he ▸ map_zero _))

lemma nonzero_s (k : Axis) : (Chart.s k).den ≠ 0 := by
  -- first leg l A coefficient in components 0,1 (64+1), l alone in 2,3
  fin_cases k <;> first | exact nonzero_of_seen _ 65 (by decide +kernel) | exact nonzero_of_seen _ 1 (by decide +kernel)
lemma nonzero_t (k : Axis) : (Chart.t k).den ≠ 0 := by
  fin_cases k <;> first | exact nonzero_of_seen _ 65 (by decide +kernel) | exact nonzero_of_seen _ 1 (by decide +kernel)

variable (K : Type*) [Field K] [Algebra K ℂ] [CharZero K]

-- names for easy inspection
noncomputable abbrev gaugeStress := ge4.image TT K
noncomputable abbrev flavorStress := ph4.image TT K
noncomputable abbrev mixedStress := mixed4.image TT K

/-- Table includes trace pivot check. No gauge variant labels in the rank certificate;
these are the class rows of the MS obtained after the Color/flavor reduction. -/
theorem pivots :
    Tables K ge4 ge5 Chart.s [1,2,3] [1,2] [1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,24,26,28,29,30]
      [1] [1,2] [1,2,3,4,5,6,7,8,10,12,13,14,15,16,17,18,19,20,21] ∧
    Tables K ph4 ph5 Chart.s [1,3] [1] [1,2,3,4,5,6,7,8,9,13,14,15,24,26]
      [] [1] [1,2,3,4,5,6,7,8,9,10,11,12,15] ∧
    Tables K mixed4 mixed Chart.t [] [1] [1,2,3,4,5,6]
      [] [] [1,2,3,4,5,6,7] := ⟨G.tables K,F.tables K,X.tables K⟩

theorem rawCounts :
    (ge4.bake TT).length = 3 ∧ (ge5.bake W).length = 4 ∧ (ge5.bake V).length = 32 ∧
    (ph4.bake TT).length = 3 ∧ (ph5.bake W).length = 4 ∧ (ph5.bake V).length = 29 ∧
    (mixed4.bake TT).length = 0 ∧ (mixed.bake W).length = 1 ∧ (mixed.bake V).length = 6 := by
  simp only [bake,G.issuers_T,G.issuers_W,G.issuers_V,F.issuers_T,F.issuers_W,F.issuers_V,
             X.issuers_T,X.issuers_W,X.issuers_V]; decide

variable {pol a b : Type} [Fintype a] [Fintype b] (C : Class pol a) (H : Class pol b) (s : Freq)

structure RowRanks (t d w v q tr' : ℕ) : Prop where
  rankT : finrank K (C.image TT K) = t
  divergence : finrank K (LinearMap.range (D K C s)) = d
  rankW : finrank K (H.image W K) = w
  rankV : finrank K (H.image V K) = v
  eq93rank : finrank K (LinearMap.range (difference K H s)) = q
  traceRank : finrank K (LinearMap.range (tr K C)) = tr'
  stays : Lands K C H s
  injectT : ∀ k, Injective ((deriv K s k).domRestrict (C.image TT K))
  twiceT : ∀ k, Injective ((deriv K s k).comp ((deriv K s k).domRestrict (C.image TT K)))
  exact94 : LinearMap.range (previous K C H s stays) = LinearMap.ker (difference K H s)
lemma finish [DecidableEq a] [DecidableEq b] {i j k l m n}
    (v : Tables K C H s i j k l m n) (h : n.length + i.length = k.length + j.length)
    (e : ∀ z, (s z).den ≠ 0) : RowRanks K C H s i.length m.length j.length k.length n.length l.length := by
  have he z : Injective ((deriv K s z).domRestrict (C.image TT K)) :=
    (Derivative.injective K s z (e z) _).comp Subtype.val_injective
  exact ⟨v.outT,v.outD,v.outW,v.outV,v.out93,v.outTrace,v.lands,he,
    fun z => (Derivative.injective K s z (e z) _).comp (he z), v.exact (e _) h⟩
theorem table9394 : RowRanks K ge4 ge5 Chart.s 3 2 2 20 19 1 ∧
    RowRanks K ph4 ph5 Chart.s 2 1 1 14 13 0 ∧
    RowRanks K mixed4 mixed Chart.t 0 0 1 6 7 0 :=
  ⟨finish K _ _ _ (G.tables K) (by decide) nonzero_s,
   finish K _ _ _ (F.tables K) (by decide) nonzero_s,
   finish K _ _ _ (X.tables K) (by decide) nonzero_t⟩

/-- No mixed T's; and every f T traceless. -/
theorem low_consequences : mixedStress K = ⊥ ∧ tr K ph4 = 0 ∧
    finrank K (LinearMap.ker (D K ge4 Chart.s)) = 1 ∧
    finrank K (LinearMap.ker (D K ph4 Chart.s)) = 1 := by
  obtain ⟨g,f,x⟩ := table9394 K
  refine ⟨Submodule.finrank_eq_zero.mp x.rankT, LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp f.traceRank), ?_, ?_⟩
  · have h := LinearMap.finrank_range_add_finrank_ker (D K ge4 Chart.s); rw [g.divergence,g.rankT] at h; omega
  · have h := LinearMap.finrank_range_add_finrank_ker (D K ph4 Chart.s); rw [f.divergence,f.rankT] at h; omega
end SatinStress.U1
