import YM.CF.Fixed.Voltage.Grant
import YM.CF.Bloom.Screen
import YM.SU5.Intrinsic.Rate.Local
/-! # R124: spend the factor exp(-B/2) and incense of the incidence sum. -/
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
set_option autoImplicit false
open Fief
-- as in size_exp (SatinThinSkyline), pay with `tip` strength
lemma height_sinks (R : Patch) : sizeK R.L 4 (fun x => Real.exp (-(1/2:ℝ)*(radiusB x:ℝ))) := by
 apply ((sizeK.tip R.L (1/4) (by norm_num)).square 2).cost_d
 filter_upwards with x; rw [abs_of_pos (Real.exp_pos _)]
 refine le_trans (b:=((tipPay (1/4) x)^2)) ?_ (le_abs_self _)
 unfold tipPay; rw [← Real.exp_nat_mul]; apply Real.exp_monotone; push_cast
 have ht:(↑(radiusB x/60):ℝ) ≤ (radiusB x:ℝ):=by exact_mod_cast (Nat.div_le_self (radiusB x) 60)
 linarith

private lemma ramifies (R : Patch) (g : ℝ → ℝ) (hg : sizeK R.L 0 g) :
    ∀ᶠ x in atTop, Real.exp (-(1/2:ℝ)*(radiusB x:ℝ))*g x ≤ dleaf R.L x := by
 have p:= (clove_p R).spine_a
 have hy := ((height_sinks R).tint hg).low (k:=2+1) (by norm_num)
 filter_upwards [pill_R (d:=1) _ zero_lt_one hy, p.eventually (ge_mem_nhds zero_lt_one), spice_R (R:=R), eventually_gt_atTop (0:ℝ)] with x hx h v t
 rw [one_mul] at hx
 unfold dleaf
 rw [div_le_iff₀ (Work.E09.temp_pos t), one_mul] at h
 apply hx.le.trans; rw [pow_two]; exact mul_le_mul_of_nonneg_left h v.2.2.le

open Rank.Thirst
abbrev peripheryCost (L:Side)(x:ℝ) := wilt (radiusB x^2)*((Real.exp 11+1)*(dleaf L x))
abbrev detectorBudget (p:BudgetPoint) := surchargeRate p (10/(p.B:ℝ)) (by positivity)

/-- What the Shop must pay. It suffices to price just the long entries, even by another
array, same sizes/coordinates. The result is for **F itself**. -/
theorem at_high_covers (R : Patch) (g : ℝ→ℝ) (hg : sizeK R.L 0 g) :
    ∀ᶠ x in atTop, ∀ (n:Side) (p:BudgetPoint) (_ : p.B=radiusB x)
    (Q Q':Sweep n→Prop) (F F':RegBudget n) (h:ℝ), 0 ≤ h →
    IncX Q F p h (dleaf R.L x) → IncX Q' F' (plusOneRate p) h (g x) →
    (∀ i : Scree.Hub n, p.B < coverNumber p.B i.val.2 → F i=F' i) →
    SupportRate (detectorBudget p) F h (peripheryCost R.L x) := by
 filter_upwards [ramifies R g hg, Work.E07.radiusB_eventually 22] with x q t n p f Q Q' F F' h hh o e u
 let z:= dleaf R.L x; let B:=p.B; let w:= (11:ℝ)/B
 have hB : 22 ≤ (B:ℝ) := Nat.cast_le.mpr (show 22 ≤ p.B from f.symm ▸ t) -- casts 22
 have hb : 0 < (B:ℝ) := Nat.cast_pos.mpr p.B_pos
 have fb:w + (1/2:ℝ) ≤ 1:=by have ht:w≤1/2:= (div_le_iff₀ hb).mpr (by linarith only [hB]); linarith
 let V:IncX Q F (surchargeRate p w (by unfold w; positivity)) h ((Real.exp 11+1)*z):= by
    apply Fixed.Voltage.upgradeI _ _ (trade_rate_far p hh (show 0 ≤ w by unfold w; positivity) (by norm_num : (0:ℝ)≤1/2) fb u o e)
    rw [show w * p.B=11 by exact div_mul_cancel₀ _ hb.ne', f]; unfold z; linarith only [q]
 unfold peripheryCost; rw [← f]; apply spend_at_incidence p hh (show 0 ≤ 10/(p.B:ℝ) by positivity) (show 0 ≤ w by unfold w; positivity) ?_ V
 unfold w B; exact le_of_eq (by ring)

/-- Compare to the scales of XXI, `wp(X)` (NOT at X+shift) and `Q=g(L,X)^2`. -/
abbrev stressWindow (x : ℝ) := Real.exp ((Real.log (Real.log x))^2)
lemma qwindow (L : Side) :
    ∀ᶠ x in atTop, dleaf L x ≤ 2 * (Scales.g SU.group L x)^2 * stressWindow x := by
 -- As in E07 `temp_coarse_le`; only need sqrt part of that test.
 let a := SU.group.slopeConstant * Real.log L.val
 have ha : 0 ≤ a := by
    have hL : 1 ≤ (L.val : ℝ) := by exact_mod_cast L.property
    exact mul_nonneg (Work.E07.slope_nonneg _) (Real.log_nonneg hL)
 filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop a] with x hx w
 have hh:0 < x+a := add_pos_of_pos_of_nonneg hx ha
 have hs: (Real.sqrt x)⁻¹ ≤ 2*(Real.sqrt (x+a))⁻¹ := by
    have ht: Real.sqrt (x+a) ≤ 2*Real.sqrt x := by
      nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hh.le, Real.sqrt_pos.2 hx]
    rw [← one_div, ← div_eq_mul_inv]; apply (div_le_div_iff₀ (Real.sqrt_pos.2 hx) (Real.sqrt_pos.2 hh)).2
    rwa [one_mul]
 let f := (Real.sqrt (x+a))⁻¹
 change f * ((Real.sqrt x)⁻¹ * stressWindow x) ≤ 2*f^2*stressWindow x
 rw [show 2*f^2*stressWindow x=f*(2*f*stressWindow x) by ring]
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) (by unfold f; positivity)

/-- The charged size, independent of torus, polynomial exponent eight here. -/
theorem periphery_bound (L : Side) : ∃ C>0, ∀ᶠ x in atTop,
    peripheryCost L x ≤ C*(1+(radiusB x:ℝ))^8 * Scales.g SU.group L x^2 * stressWindow x := by
 let c:=wilt 1 * (Real.exp 11+1)
 have hh:0≤ c:= mul_nonneg (wilty _) (by positivity)
 refine ⟨2*c+1,by positivity,?_⟩
 filter_upwards [qwindow L] with x v
 let b:ℝ:= ↑(radiusB x); have w : 0 ≤ b:= Nat.cast_nonneg _
 let z:= Scales.g SU.group L x
 have hz: 0 < stressWindow x:= Real.exp_pos _
 calc _ = c*b^8*dleaf L x:= by unfold peripheryCost c wilt b; push_cast; ring
      _ ≤ c*b^8*(2*z^2*stressWindow x):= mul_le_mul_of_nonneg_left v (by positivity)
      _ = (2*c)* b^8 * z^2 * stressWindow x:=by ring
      _ ≤ (2*c+1)*(1+b)^8 * z^2 * stressWindow x:=by gcongr <;> linarith
end YM.CF.Py
#print axioms YM.CF.Py.at_high_covers
#print axioms YM.CF.Py.periphery_bound
