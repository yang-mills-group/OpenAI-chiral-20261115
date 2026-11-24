import YM.SU5.FiniteGaugeData.Lapis.Olympia
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Artis
open Affiche ContinuousLinearMap Real
variable {n:Side}{G:Gauge} {P:Bed}{u:Stage}{R:PathData G}{a C Δ:ℝ}
local notation "Vt"=> Vault (Plush G (denim n))
-- E' not inner prod necessary; meas gaussian output.F.L.
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E][CompleteSpace E]
def Trend (L : LogField G n→ₗ[ℝ] E) := ∀ (x y:LogField G n), motive x y→ L x=L y
variable (D:Floor P u.clip n a C)(h:0<a)
-- $Olive.Symbol Price
-- use from NormedSpace finite; output E maybe require accessible
#check LinearMap.toContinuousLinearMap
def Omen(L:LogField G n→ₗ[ℝ] E): Vault (Plush G (denim n))→L[ℝ] E := (L.comp (olive D h G)).toContinuousLinearMap
local notation "H"=> olive D h G
variable (W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(L M:LogField G n→ₗ[ℝ] E)(v:Trend L)
-- transfer Reach semantics; if for right input exists left, right norm ≤ left
abbrev creditR(P:Bed)(L M:LogField G n→ₗ[ℝ] E):= ∀ x:LogField G n, ∃ y:LogField G n, L y= M x ∧ Bid.gaugeFiscal P y y ≤ Bid.gaugeFiscal P x x
include W A v
lemma lease (t: creditR P L M)(f:E→L[ℝ]ℝ) : ‖f.comp (Omen D h M)‖ ≤ ‖f.comp (Omen D h L)‖:=by
 let V:= f.comp (Omen D h L); let U:= f.comp (Omen D h M); refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_; intro x; obtain ⟨y,e,u⟩:= t (H x); obtain ⟨z,a,hz⟩:= fillC D h y; have hv:‖z‖≤ ‖x‖:= (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (le_trans (le_trans hz.ge u) (sunflower D h W A x)); apply (ContinuousLinearMap.le_opNorm V z).trans' ?_ |>.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _)) -- tune orientation
 have he:U x=V z:= by change f (M (H x)) = f (L (H z)); rw [v _ _ a, e]
 change ‖U x‖ ≤ ‖V z‖; rw [he]
local notation "μ"=> stdGaussian (Vault (Plush G (denim n)))
#check charFunDual_map
lemma prosperity (e:Trend M)(t: creditR P L M)(p: creditR P M L): Measure.map (Omen D h L) (stdGaussian (Vault (Plush G (denim n))))= Measure.map (Omen D h M) (stdGaussian (Vault (Plush G (denim n)))) :=by
 apply Measure.ext_of_charFunDual; ext x; rw [charFunDual_map,charFunDual_map,charFunDual_stdGaussian,charFunDual_stdGaussian]; -- tune
 rw [show ‖x.comp (Omen D h L)‖=‖x.comp (Omen D h M)‖ from le_antisymm (lease D h W A M L e p x) (lease D h W A L M v t x)]
lemma interest (e:Trend M)(t: creditR P L M)(p: creditR P M L)(f:E→ℝ)(hf:Measurable f): (∫ x,f (Omen D h L x)∂μ)=(∫ x,f (Omen D h M x)∂μ):= by
 rw [←integral_map (Omen D h L).continuous.measurable.aemeasurable hf.aestronglyMeasurable,← integral_map (Omen D h M).continuous.measurable.aemeasurable hf.aestronglyMeasurable]
 rw [prosperity D h W A L M v e t p]
end Artis
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Artis.interest
