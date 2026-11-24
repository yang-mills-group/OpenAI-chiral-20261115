import YM.SU5.Reconstruction.Trap.Mantle
import YM.SU5.Reconstruction.Cone.Pressure
/-!
# Actual operator norm integral & its SOT cost
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Multiplier
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {X : Type*} [MeasurableSpace X] {H : Hilbert} (P : PVM H X)
local notation "𝔪" x:max => P.diagonal x
namespace Chirp
open Complex
variable (L : X→ℝ)(m : Measurable L) (b:∀ x, 0≤ L x)(a : ℂ)(p:0<a.re)
local notation "A" => (fun z=> order P (slopeRay a L z))
noncomputable def notationT (u d:ℝ): H.Op:= - (sing (-u) d) • (deriv (fun z=> order P (slopeRay a L z)) d)
local notation "πF" i:max=> volume.restrict (page i)
noncomputable def introT (u:ℝ)(i:ℕ) : H.Op:= ∫ t in page i, notationT P L a u t ∂volume
include m b p
lemma funds (u t:ℝ)(e:0<t): Registers P (juice L a u t) (notationT P L a u t):= by
  unfold notationT; convert (rayChange P L m b a t (realRay a p t e)).scale (- (sing (-u) t)) using 1
  funext x; change a* _ * (_ * _) = - _ * _
  change a*(L x:ℂ)*(sing (-u) t*cexp (- (a*L x)*(t:ℂ))) = -(sing (-u) t)*(-a*(L x:ℂ)*cexp (-a*t*L x)); rw [show - (a*L x)*(t:ℂ) = - a*t*L x from by ring]; ring
lemma uniformPage (u:ℝ)(i:ℕ) : ∃ C:ℝ, 0 ≤ C ∧ ∀ z∈ page i,∀ x, ‖juice L a u z x‖ ≤ C:=by
 let t:= 1/((i:ℝ)+1); let T:= a.re*t; have ht:0<t:= by unfold t; positivity
 have hT:0<T:= mul_pos p ht
 -- ξ exp estimate. negative derivative multiplied by scale
 refine ⟨‖a‖*T⁻¹,by positivity,?_⟩; intro y v x
 let f:= L x; have he:f*(Real.exp (-(T*f)))≤T⁻¹:= by
   apply le_of_mul_le_mul_left _ hT; rw [mul_inv_cancel₀ hT.ne', ←mul_assoc]; linarith [ConePrice.exp_board (u:=T*f) (mul_nonneg hT.le (b x)), Real.exp_pos (-(T*f))] -- may need import
 rw [juice_norm, abs_of_nonneg (b x),mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); refine le_trans ?_ he
 apply mul_le_mul_of_nonneg_left ?_ (b x); apply Real.exp_le_exp.mpr; have h:= mul_le_mul_of_nonneg_left (show t≤y from v.1) (mul_nonneg p.le (b x)); unfold T; unfold f; linarith
lemma tunable (u:ℝ)(i:ℕ): Integrable (notationT P L a u) (volume.restrict (page i)) := by
 refine ContinuousOn.integrableOn_Icc ?_; intro t y; have z:=pagePos i y
 have r : ContinuousAt (fun t:ℝ=> deriv (fun z=> order P (slopeRay a L z)) (t:ℂ)) t:= ContinuousAt.comp (g:=fun z:ℂ=> deriv (fun z=> order P (slopeRay a L z)) z) ((bill P L m b a).deriv (t:ℂ) (realRay a p t z) |>.continuousAt) (Complex.continuous_ofReal.continuousAt)
 apply ContinuousAt.continuousWithinAt; unfold notationT; exact (sing_cont (-u) t (mem_Ioi.mp z|>.ne')).neg.smul r
lemma income (u:ℝ) (i:ℕ) : Registers P (header L a u i) (introT P L a u i) := by
 refine ⟨solid L m b a p u i,?_⟩; intro x
 let F:=notationT P L a u; let G t:=juice L a u t; let S:=page i; have hb:MeasurableSet (page i):= measurableSet_Icc
 let W:= ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space x))
 change W (∫ t, notationT P L a u t∂(volume.restrict (page i))) = ∫ p, (∫ t, G t p∂(volume.restrict (page i)))∂_
 rw [← W.integral_comp_comm (tunable P L m b a p u i)]
 refine Eq.trans (b:=∫ t, (∫ p, G t p∂𝔪 x)∂πF i) ?_ (integral_integral_swap ?_)
 · apply integral_congr_ae; filter_upwards [ae_restrict_mem (μ:=volume) hb] with t v; exact (funds P L m b a p u t (pagePos i v)).awakes x
 obtain ⟨c,d,v⟩:= uniformPage L m b a p u i; refine (integrable_const (μ:=(volume.restrict (page i)).prod (𝔪 x)) c).mono' (juice_meas L m a _|>.aestronglyMeasurable) (?_)
 filter_upwards [(MeasureTheory.Measure.quasiMeasurePreserving_fst (μ:=πF i) (ν:=𝔪 x)).ae (ae_restrict_mem (μ:=volume) hb)] with y p; exact v _ p y.2
lemma sot (u:ℝ) (x:H) : Tendsto (fun i=> introT P L a u i x) atTop (𝓝 (reward u a • (starry P L u x))) := Registers.tends atTop (fun i=>header L a u i) _ (cutoff P L m a u) (income P L m b a p u) x (‖a‖/a.re) (Eventually.of_forall fun i=> Eventually.of_forall (bounded_header L b a p u i)) (Eventually.of_forall (limit L b a p u))
end Chirp
end YM.Multiplier
