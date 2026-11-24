import YM.CF.Vp929.Analysis.Shooting

/-!
# Common UV inscriptions -- real shooting and overlap

Our volume windows for this argument will be wide in rung indices. Establish a quantitatively
uniform chamber where nearby *top* beta can be paid with *small* displacement at the terminal
height. On purpose not claiming exact terminal tuning through such a change! This is part
of an estimate on calibrated shifted shots.
-/
set_option autoImplicit false
noncomputable section

namespace YM.CF.VolumeRate.LayerOverlap
open Complex Set Function Filter Metric Topology
open Finset (range)
open scoped NNReal

variable {k:ℕ} {r d B : ℕ → ℝ} {Δ : ℕ → Bet k → ℂ} (A : Posts r d B (k:=k) Δ)
  {g : ℂ → Bet k}
local notation "S" => ball (0:ℂ) (r 0/8)
variable (b : ∀ u∈ball (0:ℂ) (r 0/8), g u ∈ area r B 1 0) (p : ∀ u∈ball (0:ℂ) (r 0/8), IsFixedPt (updateBet B Δ u) (g u))
include A b p
/-- contract only where the actual payment domain permits -/
lemma priceVariation {u v:ℂ}(hu:u∈S)(hv:v∈S):
    ‖g u - g v‖ ≤ 4/3 * ‖u-v‖ ∧ ∀ i:Fin (k+1),
      ‖g u i - g v i - (u-v)‖ ≤ 1/3 * ‖u-v‖ := by
  let C := updateBet B Δ u; let P := updateBet B Δ v
  have contract:= (A.contract v).dist_le_mul (g u) (b u hu) (g v) (b v hv)
  simp only [dist_eq_norm] at contract
  change ‖P _ - P _‖ ≤ _ at contract
  push_cast at contract
  have compare (i:Fin (k+1)) : (C (g u)) i - (P (g u)) i = u-v := by dsimp [C,P,updateBet]; ring
  have hk (i:Fin (k+1)): g u i - g v i = u-v + (P (g u) - P (g v)) i := by
    change _ = _ + (P (g u) i - P (g v) i)
    rw [← compare i]
    rw [show C (g u) = g u from p u hu, show P (g v) = g v from p v hv]; ring
  have z (i:Fin (k+1)):= le_trans (norm_le_pi_norm (P (g u)-P (g v)) i) contract
  have hW: ‖g u - g v‖ ≤ ‖u-v‖ + 1/4 * ‖g u-g v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=>?_
    change ‖g u i - g v i‖ ≤ _; rw [hk]; exact (norm_add_le ..).trans (add_le_add_right (z i) _)
  have l : ‖g u - g v‖ ≤ 4/3 * ‖u-v‖ := by linarith
  refine ⟨l,fun i=>?_⟩; rw [hk,add_sub_cancel_left]; exact (z i).trans (by linarith)

lemma positiveSlopes {x y:ℝ} (u : (x:ℂ) ∈ S) (v : (y:ℂ) ∈ S) (h:x≤y) (i:Fin (k+1)) :
    2/3*(y-x) ≤ (g y i).re - (g x i).re ∧ (g y i).re - (g x i).re ≤ 4/3*(y-x) := by
  have hp:= (abs_re_le_norm (g y i-g x i- ((y:ℂ)-x))).trans ((priceVariation A b p v u).2 i)
  rw [← ofReal_sub,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h), sub_re, sub_re, ofReal_re] at hp
  exact ⟨by linarith [(abs_le.mp hp).1],by linarith [(abs_le.mp hp).2]⟩

-- Tuning in the convention of the problem, on the top value only here.
def topPrice (g : ℂ → Bet k) (z:ℝ) := (g z (Fin.last k)).re
lemma strict_chamber : StrictMonoOn (topPrice g) (Ioo (-(r 0/8)) (r 0/8)) := by
  have hc (z:ℝ)(p:z∈ Ioo (-(r 0/8)) (r 0/8)): (z:ℂ) ∈ S := by
    rw [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs]; exact abs_lt.mpr ⟨p.1,p.2⟩
  intro i u j v t
  have hL:2/3*(j-i) ≤ topPrice g j - topPrice g i := (positiveSlopes A b p (hc i u) (hc j v) t.le (Fin.last k)).1; linarith

/-- Standard normalization around any official zero-offset shot. Use it in either
sign. `β` here is the *top* parameter of a trajectory. -/
theorem feasible_payment (dG : ContinuousOn g S) (ε:ℝ) (h : 0< ε)(hε:ε<r 0/8)
    (β:ℝ)(pβ: |β-topPrice g 0| ≤ ε/2) : ∃ z:ℝ, |z|≤ ε ∧ topPrice g z=β := by
  have zero : (↑(0:ℝ):ℂ)∈ S := by rw [mem_ball_zero_iff]; simp; linarith
  let X:= Set.Icc (-ε) ε
  have posX (x:ℝ): x∈ X ↔ |x|≤ε := abs_le.symm
  have hc : MapsTo ((↑):ℝ→ℂ) X S := fun z p=> by rw [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs]; exact lt_of_le_of_lt ((posX _).mp p) hε
  have hed:-ε ≤ ε := by linarith
  have d: ContinuousOn (topPrice g) X := continuous_re.continuousOn.comp
        ((continuous_apply (A:=(fun _:Fin (k+1)=>ℂ)) (Fin.last k)).continuousOn.comp (dG.comp ofRealCLM.continuous.continuousOn hc) (mapsTo_univ _ _)) (mapsTo_univ _ _)
  have ht:= (positiveSlopes A b p zero (hc (right_mem_Icc.mpr hed)) h.le (Fin.last k)).1
  have he:= (positiveSlopes A b p (hc (left_mem_Icc.mpr hed)) zero (neg_nonpos.mpr h.le) (Fin.last k)).1
  change _ ≤ topPrice g ε-topPrice g 0 at ht
  change _ ≤ topPrice g 0-topPrice g _ at he
  obtain ⟨z,u,v⟩:= intermediate_value_Icc hed d (show β∈ _ from
    (Set.mem_Icc.mpr ⟨by linarith [(abs_le.mp pβ).1],by linarith [(abs_le.mp pβ).2]⟩))
  exact ⟨z,(posX _).mp u,v⟩

end YM.CF.VolumeRate.LayerOverlap
end
#print axioms YM.CF.VolumeRate.LayerOverlap.feasible_payment
