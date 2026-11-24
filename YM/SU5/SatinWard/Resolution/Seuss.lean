import YM.SU5.MacroSix.Grid
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Function Finset Metric Filter ENNReal MeasureTheory
open scoped Topology NNReal ENNReal BigOperators ContDiff
noncomputable section
namespace GarnetAct.Cut
local notation "G"=> (Fin 4 → ℝ)
local notation "W"=> (Fin 4 → ℤ)
/-! Pos test densities.Real.( ℓ∞ metric Euclidean measure). -/
structure Curtain where
  val : G → ℝ
  classy : ContDiff ℝ ∞ val
  budget : HasCompactSupport val
  positive (x:G) :0 ≤ val x
  mass : (∫ x:G,val x)=1

namespace Curtain
variable (F:Curtain)
abbrev boxS : Set G := tsupport F.val
lemma ownsK : IsCompact F.boxS:= F.budget
lemma ownsV : Integrable F.val:= F.classy.continuous.integrable_of_hasCompactSupport F.budget
noncomputable abbrev ppm : Measure G:= volume.withDensity fun x=> ENNReal.ofReal (F.val x)
noncomputable instance : IsProbabilityMeasure F.ppm:= ⟨by
    unfold ppm; rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal F.ownsV (ae_of_all _ F.positive),F.mass,ENNReal.ofReal_one]⟩ -- need measurableSet_univ syntax.
lemma wallet : AEMeasurable (fun x=> ENNReal.ofReal (F.val x)) volume:= (ENNReal.continuous_ofReal.comp F.classy.continuous).aemeasurable
lemma inhabits : ∀ᵐ x ∂ F.ppm,x∈ F.boxS:= by
 apply (ae_withDensity_iff' F.wallet).2; filter_upwards with x h; apply subset_tsupport F.val; intro u; exact h (by rw [show F.val x=0 from u,ENNReal.ofReal_zero])
lemma honest {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X](A:G→ X) : ∫ x:G,A x ∂ F.ppm=∫ x:G,F.val x • A x:=by
 unfold ppm; rw [integral_withDensity_eq_integral_toReal_smul₀ F.wallet]; · simp_rw [ENNReal.toReal_ofReal (F.positive ..)] -- perhaps no goal
 exact ae_of_all _ fun _=>ENNReal.ofReal_lt_top -- `_`
-- actual assignments use ANY G with support inside Fin compact.Core.Tool.
lemma grows (x:G)(u:ℝ)(v:0<u): ∃ F:Curtain,F.boxS=closedBall x u:=by
 let f:ContDiffBump x:=⟨u/2,u,half_pos v,half_lt_self v⟩; let d:= f.normed volume; let R:Curtain:=⟨d,f.contDiff_normed,f.hasCompactSupport_normed,fun t=> f.nonneg_normed _,f.integral_normed⟩; exact ⟨R,f.tsupport_normed_eq⟩
end Curtain
end GarnetAct.Cut
