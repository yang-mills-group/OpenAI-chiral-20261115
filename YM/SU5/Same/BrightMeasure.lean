import YM.SU5.Same.EnergySheet
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
/-! # The true Mink positive-time spectral occupation measure. Veers into strict
Eucl when heating but not analytic at offset assumed at the limit.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical
open Multiplier Roy
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert} {a:Axis}(S:OS.Semigroup H a) (X:ℝ→ H)
local notation "P" => S.ℚmeasure
local notation "B" n:max => foldBand a n
local notation "θ" => S.ℚmeasure.diagonal
local notation "Z" n:max => wing S X n

/-- Unoffset. Polynomial budget applies with the M3p regular ballot powers. -/
def homeMeasure : Measure E4 := Measure.sum (fun i=> (θ) (Z i))
local notation "μ₀" => homeMeasure S X
lemma home_carried : ∀ᵐ p:E4 ∂(homeMeasure S X), 0≤ p a := by
 unfold homeMeasure; rw [ae_sum_iff]; exact fun i=> S.bright (Z i)
lemma home_strict_time (h:∀ i:ℕ, (P).region (toe a) (X (minute i:ℝ))=0) : ∀ᵐ p ∂μ₀,0 < p a:=by
 unfold homeMeasure; rw [ae_sum_iff]; intro i
 have hz:(P).region (toe a) (Z i)=0:=by
    unfold wing
    rw [show (P).region (toe a) (rewarm S (minute i) i (X (minute i:ℝ)))= rewarm S (minute i) i ((P).region (toe a) (X (minute i:ℝ))) from DFunLike.congr_fun ((rewarm_reads S (minute i) i).comm toe_meas).eq.symm _,h,map_zero]
 have he: ∀ᵐ p∂(P).diagonal (Z i), p∉ toe a:= ae_iff.mpr (by push Not; exact ((P).null_pair toe_meas _).mpr hz)
 exact ((S.bright _).and he).mono fun x p=> lt_of_le_of_ne p.1 (show 0≠ x a from (show x a≠0 from p.2).symm)
lemma ae_wing (i:ℕ):∀ᵐ p∂(P).diagonal (wing S X i),p∈ B i:=by
 nth_rw 1 [← wing_fixed S X i]
 rw [ConePrice.restrictP S (foldBand_meas i)]; exact ae_restrict_mem (foldBand_meas i)
lemma wing_power (h:TemperedAtEdge H X):∃ m:ℕ,∃ C≥(0:ℝ),∀ i:ℕ, ((θ) (Z i)).real Set.univ ≤ C*((i+1:ℕ):ℝ)^m:=by
 obtain ⟨m,C,h,c⟩:= wing_grows S X h; refine ⟨m*2,C^2,sq_nonneg _,fun i=>?_⟩; rw [Registers.size,pow_mul (↑(i+1):ℝ),←mul_pow]; exact pow_le_pow_left₀ (norm_nonneg (Z i)) (c i) _

/-- The estimate uses only the ENERGY slabs (not weaker since doesn't need
  covering in spatial coordinates at each moment price). It pays `measure_sum_measure`
  integrability. For full ℝ^4 TEMPER on test spaces buy via |p|≥energy. -/
lemma currency (h:TemperedAtEdge H X): ∃ n:ℕ, Integrable (fun p:E4=> ((1+timeOf a p)^n)⁻¹) μ₀:=by
 obtain ⟨m,C,v,w⟩:= wing_power S X h; let n:= m+2; let f(p:E4):= ((1+timeOf a p)^n)⁻¹; let T (i:ℕ):=((i+1:ℕ):ℝ)
 have he(i):0<T i:=by unfold T; positivity
 have ht(p:E4):0≤timeOf a p:=le_max_left ..
 have hx(p:E4): 1 ≤ (1+timeOf a p)^n:= one_le_pow₀ (by linarith only [ht p])
 have hy(p:E4): 0< f p:= inv_pos.mpr (zero_lt_one.trans_le (hx p))
 have hf : Continuous f:=by
    refine Continuous.inv₀ ((continuous_const.add tick_cont).pow _) fun p=> (zero_lt_one.trans_le (hx p)).ne'
 have hp:∀ i:ℕ, Integrable f ((θ) (Z i)):= fun i=> Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun p=> (Real.norm_of_nonneg (hy p).le).trans_le (inv_le_one_of_one_le₀ (hx p)))
 refine ⟨n,integrable_sum_measure hp ?_⟩
 have h1:Summable (fun i:ℕ=> C*((T i)^2)⁻¹):= ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv (p:=2)|>.2 (by norm_num))).mul_left _
 refine h1.of_nonneg_of_le (fun i=>integral_nonneg (fun p=> norm_nonneg _)) fun i=>?_
 let g:=(θ) (Z i)
 let t:= T i
 have hd: (∫ p, ‖f p‖∂g) ≤ g.real Set.univ*(t^n)⁻¹:=by
    have h' : (∫ p, ‖f p‖∂g)≤ ∫ p:E4, (t^n)⁻¹ ∂g:= integral_mono_ae (hp i|>.norm) (integrable_const _) ((ae_wing S X i).mono (fun p b=>?_))
    · exact h'.trans_eq (by rw [integral_const]; rfl)
    change ‖f p‖ ≤ (t ^ n)⁻¹; rw [Real.norm_of_nonneg (hy p).le]; have hb:t≤1+timeOf a p:=by
      have hv : (i:ℝ)≤ timeOf a p:= b.1; unfold t T; push_cast; linarith only [hv]
    exact inv_anti₀ (pow_pos (he i) n) (pow_le_pow_left₀ (he i).le hb _)
 calc ∫ p, ‖f p‖ ∂ g ≤ g.real Set.univ * (t^n)⁻¹:= hd
      _ ≤ C*t^m * (t^n)⁻¹ := mul_le_mul_of_nonneg_right (w i) (inv_nonneg.mpr (pow_nonneg (he i).le _))
      _ = C * (t^2)⁻¹:= by rw [show n=m+2 from rfl,pow_add]; field_simp [pow_ne_zero m (show t ≠ 0 from (he i).ne'),show t≠0 from (he i).ne']

lemma tempered_home (h:TemperedAtEdge H X): (homeMeasure S X).HasTemperateGrowth:=by
 obtain ⟨n,b⟩:= currency S X h; refine ⟨n,(b.mono' (Continuous.aestronglyMeasurable (show Continuous (fun x:E4=> (1+‖x‖) ^ (-(n:ℝ))) from (continuous_const.add continuous_norm).rpow_const fun x=> Or.inl (by change 1+‖x‖≠0; positivity))) (Eventually.of_forall fun p=> ?_))⟩
 have he:0<1+timeOf a p:=by linarith only [show 0≤timeOf a p from le_max_left ..]
 have hx:0<1+‖p‖:= by positivity
 rw [Real.norm_of_nonneg (by positivity),Real.rpow_neg hx.le,Real.rpow_natCast]; exact inv_anti₀ (pow_pos he n) (pow_le_pow_left₀ he.le (add_le_add le_rfl (timeOf_bound p)) n)

-- density laws. Use real value when possible. No interpretation on negative times needed.
lemma fee_density {U:H.Op}{f:E4→ℂ}(h:Registers S.ℚmeasure f U)(x:H) : (P).diagonal (U x)= ((P).diagonal x).withDensity (fun p=> ENNReal.ofReal (‖f p‖^2)):=by
 ext s hs; rw [←ofReal_measureReal (measure_ne_top _ _)]; rw [h.takes hs] -- order takes hs?
 refine Eq.trans ?_ (withDensity_apply _ hs).symm; refine ofReal_integral_eq_lintegral_ofReal ?_ (ae_of_all _ (fun i=>sq_nonneg _)); let p:= h.price.meas; obtain ⟨c,t,f₀⟩:= h.price.bound
 apply Integrable.of_bound ((p.norm.pow_const 2).aestronglyMeasurable) (c^2) (ae_of_all _ (fun i=>?_)); rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (f₀ i) _

abbrev coloring (a:Axis)(t:ℝ≥0)(p:E4):= (favor a t p)^2
abbrev coloringE (a:Axis)(t:ℝ≥0)(p:E4) := ENNReal.ofReal (coloring a t p)
@[fun_prop] lemma continuous_color (t:ℝ≥0): Continuous (coloring a t):=(Roy.favorC t).pow 2
lemma exact_density (h:SatinJets.Positive S X)(t:ℝ≥0)(u:0<t): (P).diagonal (X t)= (μ₀).withDensity (coloringE a t):=by
 apply (measure_sum_booths ((P).diagonal (X t)) (a:=a)).trans
 unfold homeMeasure; rw [withDensity_sum]; apply congrArg Measure.sum; funext i
 rw [← ConePrice.restrictP S (foldBand_meas i)]; change (θ) (cell S i (X t)) = _; rw [←wing_earns S X h t u, fee_density S (costT S t)]; simp_rw [Complex.norm_real,Real.norm_of_nonneg (favorL _ _).1.le]
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms exact_density
#print axioms home_strict_time
#print axioms tempered_home
