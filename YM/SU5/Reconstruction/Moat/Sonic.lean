import YM.SU5.Reconstruction.Moat.Diode
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Moat
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup ConePrice
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
local notation "D" p:max t:max => Real.exp (-(p a)*(t:ℝ))
noncomputable def note (x:H)(t:ℝ≥0)(y: Cross a):= inner ℂ x (S.U y (S.E t x))
lemma note_cap {C:ℝ}{x:H}(p:‖x‖≤C)(t:ℝ≥0)(y: Cross a): ‖note S x t y‖ ≤ C*C:= (norm_inner_le_norm ..).trans (mul_le_mul p ((ticket_bound S y t x).trans p) (norm_nonneg _) ((norm_nonneg _).trans p))
def tariff (x:H)(t:ℝ≥0)(y:Cross a):=(note S x 0 y-note S x t y).re
lemma tariff_cap {C:ℝ}{x:H}(p:‖x‖≤C)(t:ℝ≥0)(y: Cross a): tariff S x t y≤ 2*C^2 := calc
 _ ≤ ‖note S x 0 y-note S x t y‖:= Complex.re_le_norm _
 _ ≤ _:= (norm_sub_le ..).trans ((add_le_add (note_cap S p 0 y) (note_cap S p t y)).trans_eq (by ring))

def pollen (x:Cross a)(t:ℝ≥0)(p:E4):ℝ:= amplitude x 0 p-amplitude x t p
lemma pay {x:H}(t:ℝ≥0)(y:Cross a) : tariff S x t y= ∫ p, pollen y t p ∂𝔪 x:=by unfold tariff note pollen; rw [Complex.sub_re,warm,warm,integral_sub (amp_can ..) (amp_can ..)]
lemma probate (x:H)(t:ℝ≥0)(y:Cross a) : tariff S x t (-y)=tariff S x t y:=by rw [pay,pay]; simp [pollen,amplitude]
lemma pollen_meets (t:ℝ≥0)(y:Cross a)(p:E4): pollen y t p=(1-Real.exp (- (p a)*(t:ℝ))) * Real.cos (inner ℝ (SEP a p) y):=by unfold pollen amplitude; rw [cone_mean]; simp only [NNReal.coe_zero,mul_zero,Real.exp_zero,mul_one]; ring
open Finset
variable {ι:Type}[Fintype ι] (x:ι→Cross a) (r:ℝ≥0)(u v:ℝ)
local notation "N"=> Fintype.card ι
noncomputable def wavelet (p:E4):= ∑ i, ∑ j, pollen (x i-x j) r p
lemma wave_sum (p:E4): wavelet x r p=(1-D p r) * ∑ i,∑ j, Real.cos (inner ℝ (SEP a p) (x i - x j)):= by simp_rw [Finset.mul_sum, ← pollen_meets]; rfl
private lemma cushion (p:E4):0 ≤ ∑ i,∑ j, Real.cos (inner ℝ (SEP a p) (x i - x j)) := by
 let f (i:ι):= Real.cos (inner ℝ (SEP a p) (x i)); let g (i:ι):= Real.sin (inner ℝ (SEP a p) (x i))
 convert! add_nonneg (sq_nonneg (∑ i, f i)) (sq_nonneg (∑ i, g i)) using 1
 simp_rw [inner_sub_right, Real.cos_sub, sum_add_distrib]; simp only [pow_two, sum_mul,mul_sum,f,g]; exact congrArg₂ (· + ·) (sum_comm) (sum_comm)
lemma wave_nonneg (p:E4)(h:p∈front a):0 ≤ wavelet x r p:= by
 rw [wave_sum]; exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by have v:0≤ p a:= (norm_nonneg _).trans h; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr v) (by positivity)))) (cushion x p)

def band (a: Axis) (u v:ℝ): Set E4:={x|u ≤ x a ∧ x a ≤ v}
lemma bandM (a:Axis)(u v:ℝ): MeasurableSet (band a u v):= (show IsClosed (band a u v) from (isClosed_le (continuous_const (y:=u)) (by fun_prop : Continuous (fun x:E4=> x a))).inter (isClosed_le (by fun_prop : Continuous (fun x:E4=> x a)) continuous_const)).measurableSet
local notation "vV"=> band a u v
lemma wave_plant (p:E4)(h: p∈front a)(e:p∈ band a u v)(f:∀ i j:ι, v*‖x i-x j‖≤ 1) {A: ℝ}(q:0≤A) (D':A* (r:ℝ) ≤ 1- Real.exp (-u*(r:ℝ))): N^2 / (2:ℝ)*(A*(r:ℝ)) ≤ wavelet x r p:=by
 rw [wave_sum,mul_comm (1-_ : ℝ)]
 have he : A*(r:ℝ) ≤ 1- (D p r):= D'.trans (sub_le_sub_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg e.1) (by positivity))) _)
 apply mul_le_mul _ he (by positivity)
 · exact (cushion x p)
 -- check order
 calc
    _ = ∑ _ : ι,∑ _ : ι, (2:ℝ)⁻¹:=by simp only [sum_const, card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum fun i _=> sum_le_sum fun j _=> by
      have hm : |inner ℝ (SEP a p) (x i-x j)| ≤ 1:= (abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_right ((show ‖SEP a p‖ ≤ p a from h).trans e.2) (norm_nonneg _)).trans (f i j))
      have hv:= Real.one_sub_sq_div_two_le_cos (x:=inner ℝ (SEP a p) (x i -x j)); nlinarith [(abs_le.mp hm).1,(abs_le.mp hm).2]

lemma song (χ:H): ∑ i,∑ j, tariff S χ r (x i-x j)=∫ p,wavelet x r p ∂𝔪 χ:=by
 have he (i:ι)(j:ι): Integrable (pollen (x i-x j) r) (𝔪 χ):= (amp_can ..).sub (amp_can ..)
 simp_rw [wavelet, integral_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=> he i j)), integral_finsetSum _ (fun j _=> he _ j), pay]

variable (Q: Forward S) (f:∀ i j:ι, v*‖x i-x j‖≤ 1) {A: ℝ} (q:0≤A) (D':A * (r:ℝ) ≤ 1 - Real.exp (-u*(r:ℝ)))
include Q f q D'
lemma bandCost (χ:H): (N:ℝ)^2/2*(A*(r:ℝ))*‖(P).region (band a u v) χ‖^2 ≤ ∑ i,∑ j, tariff S χ r (x i-x j):= by
 rw [song,← (P).same (bandM a u v)]; set B:= (N:ℝ)^2 /2*(A*(r:ℝ)); apply le_trans _ (integral_mono_ae ((integrable_const (μ:=𝔪 χ) B).indicator (bandM a u v)) (show Integrable (wavelet x r) (𝔪 χ) from integrable_finsetSum _ (fun _ _=> integrable_finsetSum _ (fun _ _=>?_))) ?_)
 · rw [integral_indicator (bandM ..), setIntegral_const, smul_eq_mul]; exact (mul_comm ..).le
 · exact ((forward_ae S χ Q).mono fun p Hp => by
       by_cases t:p∈ vV
       · rw [Set.indicator_of_mem t]; exact wave_plant x r u v p Hp t f q D'
       rw [Set.indicator_of_notMem t]; exact wave_nonneg x r p Hp)
 exact Integrable.sub (amp_can ..) (amp_can ..)
end YM.Moat
