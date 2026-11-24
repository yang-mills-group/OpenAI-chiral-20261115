import YM.SU5.Registration.Tariff
import YM.SU5.Same.RollCall
import YM.SU5.FiniteGaugeData.Seld.WildCat

/-!
# Pricing on the real sector

We do not assume a relation to a separately reconstructed Wightman Hilbert
space or a cone bound. For the actual real-sheet calculation: relate Seld's
heat resolvent estimate to energy-band cutting & composing insertions. Obtain
the domain tariffs from the Seld `brochure` theorem (which implements time
integration by parts) and polynomial growth of just the point blocks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet
open Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "U" => S.unit.translation

def bands : Grading H where
  «P» := cell S
  real := fun n=> (P).real (foldBand_meas n)
  same := fun n=> by ext1 x; exact PVM.idempotent P (foldBand_meas n) x
  other {m n} h := by
    rw [(P).joins (foldBand_meas m) (foldBand_meas n), Set.disjoint_iff_inter_eq_empty.mp (foldBand_disjoint a h),(P).none]
  sum := voting S
@[simp] lemma band (n : ℕ) : (bands S).P n = cell S n := rfl

lemma band_inverse_sym (t : ℝ≥0) (n : ℕ) : (rewarm S t n).adjoint = rewarm S t n := by
  apply Registers.single (rewarm_reads S t n|>.adjoint)
  rw [show star (charging a t n) = charging a t n from ?_]; exact rewarm_reads S t n
  ext1 x; by_cases h:x∈foldBand a n <;> simp only [charging,Pi.star_apply,indicator_of_mem,indicator_of_notMem,h,not_false_eq_true,star_zero,Complex.star_def,Complex.conj_ofReal]

def resolventWeight (a : Axis) (p : E4) : ℝ := 1+timeOf a p
lemma weight_ge (a : Axis) (p : E4) : 1 ≤ resolventWeight a p :=
  le_add_of_nonneg_right (le_max_left ..)
lemma resolvent_weight_pos (a : Axis) (p : E4) : 0 < resolventWeight a p := zero_lt_one.trans_le (weight_ge a p)
@[fun_prop] lemma continuous_resolventWeight (a : Axis) : Continuous (resolventWeight a) := by unfold resolventWeight; fun_prop

def mild (a : Axis) (p : E4) : ℂ := (((resolventWeight a p)⁻¹:ℝ):ℂ)
lemma tag_mild : Tag (mild a) := by
  have he : Continuous (mild a) := Complex.continuous_ofReal.comp
    ((continuous_resolventWeight a).inv₀ (fun p=>(resolvent_weight_pos a p).ne'))
  refine ⟨he.measurable,1, zero_le_one, fun x=>?_⟩
  simp only [mild,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (resolvent_weight_pos _ _).le)]; exact inv_le_one_of_one_le₀ (weight_ge _ _)
lemma saucer_reads : Registers S.ℚmeasure (mild a) (saucer S) := by
  refine ⟨tag_mild,fun x=>?_⟩
  let μ:=(P).diagonal x
  haveI:IsFiniteMeasure μ:= PVM.finite P x
  let F(t:ℝ)(p:E4): ℂ := ↑(Real.exp (-t)*favor a t.toNNReal p)
  have ht (t:ℝ) : inner ℂ x (cups S x t) = ∫ p:E4,F t p∂μ := by
    change inner ℂ x ((Real.exp (-t):ℂ) • S.E t.toNNReal x) = _
    rw [inner_smul_right, (costT S t.toNNReal).awakes, ← integral_const_mul]; unfold F; push_cast; rfl
  let ν := (volume (α:=ℝ)).restrict (Set.Ioi 0)
  have hF: Integrable (uncurry F) (ν.prod μ):= by
    have he:= (show Integrable _ ν from integrableOn_exp_neg_Ioi (0:ℝ)).mul_prod (show Integrable (fun _ : E4=> (1:ℝ)) μ from integrable_const _)
    have hx: Continuous (uncurry F):= by unfold uncurry F favor; fun_prop
    apply he.mono' hx.aestronglyMeasurable
    filter_upwards with w
    change ‖F w.1 w.2‖ ≤ Real.exp (-w.1)*1
    unfold F; rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (favorL _ _).1.le)]; exact mul_le_mul_of_nonneg_left (favorL _ _).2 (Real.exp_pos _).le
  have hp(p:E4): (∫ t:ℝ,F t p∂ν)=mild a p:=by
    have hw:=resolvent_weight_pos a p
    trans ∫ t:ℝ in Set.Ioi (0:ℝ), (↑(Real.exp (-(resolventWeight a p)*t)):ℂ)
    · refine integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t h=>?_); dsimp only; unfold F favor; rw [← Real.exp_add,Real.coe_toNNReal _ (show 0≤t from (show 0<t from h).le)]; unfold resolventWeight timeOf; congr 2; ring
    rw [integral_complex_ofReal,integral_exp_mul_Ioi (neg_lt_zero.mpr hw)]; simp [mild]
  rw [saucer_apply, ship, ←integral_inner (cupsI S x)]; simp_rw [ht]; rw [integral_integral_swap hF]; exact integral_congr_ae (Eventually.of_forall hp)

lemma cache_reads (k : ℕ) : Registers S.ℚmeasure ((mild a)^k) (Cache S k) := by
  unfold Cache
  induction k with
  | zero => rw [pow_zero,pow_zero]; exact Registers.one _
  | succ k ih => rw [pow_succ,pow_succ]; exact ih.times (saucer_reads S)

local notation "G" => bands S
abbrev fade (k n : ℕ) := cell S n * Cache S k
lemma fade_cost (k n : ℕ) : ‖fade S k n‖ ≤ (weight k n)⁻¹ := by
  apply Registers.fare ((Registers.box (P) (foldBand_meas n)).times (cache_reads S k)) (inv_nonneg.mpr (weight_pos k n).le)
  intro x
  by_cases h:x∈foldBand a n
  · simp only [Pi.mul_apply,indicator_of_mem h,Pi.one_apply,one_mul,Pi.pow_apply,mild,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (resolvent_weight_pos _ _).le),inv_pow]
    apply inv_anti₀ (weight_pos k n) (pow_le_pow_left₀ (by positivity) ?_ _)
    have he: (n:ℝ)≤timeOf a x := h.1
    unfold resolventWeight; push_cast; linarith
  simp only [Pi.mul_apply,indicator_of_notMem h,zero_mul,norm_zero]; exact inv_nonneg.mpr (weight_pos k n).le

def owe (k n : ℕ) (a : Axis) := (foldBand a n).indicator (fun p=> ((↑(resolventWeight a p):ℂ))^k)
lemma owe_price (k n : ℕ) (p : E4) : ‖owe k n a p‖ ≤ weight k (n+1) := by
  by_cases e:p∈foldBand a n
  · have he: timeOf a p ≤ (↑(n+1:ℕ):ℝ) := (show timeOf a p < (↑(n+1:ℕ):ℝ) from e.2).le
    simp only [owe, indicator_of_mem e,norm_pow,Complex.norm_real,Real.norm_of_nonneg (resolvent_weight_pos a p).le]
    apply pow_le_pow_left₀ (resolvent_weight_pos a p).le ?_ _
    unfold resolventWeight; rw [add_comm, Nat.cast_add_one]
    gcongr
  simp only [owe,indicator_of_notMem e,norm_zero]; exact (weight_pos k (n+1)).le
lemma owe_tag (k n : ℕ) : Tag (owe k n a) := ⟨Measurable.indicator (by fun_prop) (foldBand_meas n),_,(weight_pos k (n+1)).le, owe_price k n⟩
abbrev burn (k n : ℕ) := order S.ℚmeasure (owe k n a)
lemma cache_clear (k n : ℕ) : Cache S k * burn S k n = cell S n := by
  apply Registers.single ((cache_reads S k).times (order_reads _ (owe_tag k n)))
  have he : (mild a)^k * owe k n a = (foldBand a n).indicator (1:E4→ℂ):= by
    ext1 p; by_cases e:p∈foldBand a n
    · simp only [Pi.mul_apply,Pi.pow_apply,mild,owe,indicator_of_mem e,Pi.one_apply,←mul_pow,←Complex.ofReal_mul,inv_mul_cancel₀ (resolvent_weight_pos a p).ne',Complex.ofReal_one,one_pow]
    simp only [Pi.mul_apply,owe,indicator_of_notMem e,mul_zero]
  rw [he]; exact Registers.box _ (foldBand_meas n)
lemma burn_cost (k n : ℕ) : ‖burn S k n‖ ≤ weight k (n+1) := Registers.fare (order_reads _ (owe_tag k n)) (weight_pos k (n+1)).le (owe_price k n)
-- Seld.apron smears with full (strongly continuous) Mink translations S.unit
-- on this Hilbert; neither an op-norm integral nor the Euclidean probe weights.

lemma translate_cell (p : E4) (m : ℕ) : Commute (U p) (cell S m) :=
  (Picket.story S p).comm (foldBand_meas m)
lemma heat_commutes (t : ℝ≥0) (p : E4) : Commute (S.E t) (U p) :=
  (costT S t).jointly (Picket.story S p)
lemma heat_cell (t : ℝ≥0) (n : ℕ) : Commute (S.E t) (cell S n) :=
  (costT S t).comm (foldBand_meas n)

variable (B : (bands S).Blocks)
def smearedBlocks (f : Test4) : (G).Blocks where
  op m n := apron S (B.op m n) f
  out m n := by
    change cell S m * valise S _ f = valise S _ f
    rw [← overlap S (B.op m n) (cell S m) f (fun p=> translate_cell S p m),
      show cell S m*B.op m n=B.op m n from B.out m n]
  inlet m n := by
    change valise S _ f * cell S n = valise S _ f
    rw [← overlap_R S (B.op m n) (cell S n) f (fun p=> translate_cell S p n),
      show B.op m n*cell S n=B.op m n from B.inlet m n]

lemma smear_bounded (B : H.Op) (f : Test4) : smearedBlocks S ((G).dissect B) f= (G).dissect (valise S B f) := by
  ext1
  funext m n
  change valise S (cell S m*B*cell S n) f= cell S m*valise S B f*cell S n
  rw [overlap_R,overlap]
  · exact fun p=>translate_cell S p m
  · exact fun p=>translate_cell S p n

lemma dolly_nonneg (a : Axis) (k : ℕ) (f : Test4) : 0 ≤ dollycoin a k f := by induction k generalizing f with
 | zero => exact norm_nonneg _
 | succ k ih => exact add_nonneg (ih _) (ih _)

-- Hilbert power smoothing obtained even if there is no estimate in
-- spatial momentum. This will license the `Grading.Tariff` summations.
lemma late_light (f : Test4) (m n k : ℕ) :
    weight k m * ‖(smearedBlocks S B f).op m n‖ ≤ dollycoin a k f * ‖B.op m n‖ * weight k (n+1) := by
  let K:= B.op m n
  let X:=(smearedBlocks S B f).op m n
  let V:=Cache S k
  let L:=brochure S K k f
  let W:=fade S k m
  let Z:=burn S k n
  have hx:X = W*L*Z := by
    have hu: cell S m*X=X:=(smearedBlocks S B f).out m n
    calc X = cell S m * (X * cell S n) := by rw [show X*cell S n=X from (smearedBlocks S B f).inlet m n,hu]
         _ = W*L*Z := by rw [←cache_clear S k n,←mul_assoc X, show X*Cache S k=_ from brochure_eq S K f k]; simp only [W,fade,L,Z,mul_assoc]
  change weight k m * ‖X‖≤_
  rw [hx]
  calc weight k m * ‖W*L*Z‖ ≤ weight k m * ((‖W‖*‖L‖)*‖Z‖) := 
              mul_le_mul_of_nonneg_left ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (norm_mul_le W L) (norm_nonneg _))) (weight_pos k m).le
       _ ≤ weight k m * (((weight k m)⁻¹ * (dollycoin a k f*‖K‖))*weight k (n+1)) := by
              have h1: ‖W‖ ≤ (weight k m)⁻¹ := fade_cost S k m
              have h2: ‖L‖ ≤ dollycoin a k f * ‖K‖:= dollyP S K f k
              have h3:= burn_cost S k n
              exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)) h3 (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans h1) ((norm_nonneg _).trans h2))) (weight_pos _ _).le
       _ = _ := by dsimp only [K]; field_simp [(weight_pos k m).ne']

/-- Polynomial price before real test (generous separate powers).
Does not assert a price of that form if not known on the *operator blocks*.
-/
def PowerPrice (r : ℕ) (C : ℝ) : Prop := ∀ m n, ‖B.op m n‖ ≤ C * weight r m * weight r n
def PowerPaid : Prop := ∃ r C, 0≤C ∧ PowerPrice S B r C
variable (r k : ℕ) (C : ℝ) (f : Test4)
abbrev meterLoss (a : Axis) := ((2:ℝ)^(k+2+r)) * C * dollycoin a (k+2+r) f
lemma meter_continuous (a : Axis) : Continuous (fun f : Test4=> meterLoss r k C f a) :=
  (dollyC (a:=a) (k+2+r)).const_mul _
lemma meter_nonneg (h : 0≤C) : 0 ≤ meterLoss r k C f a := mul_nonneg (mul_nonneg (by positivity) h) (dolly_nonneg a _ f)
lemma meter_zero (a : Axis) : meterLoss r k C 0 a=0:=by unfold meterLoss; rw [dollyZ,mul_zero]
private lemma next_le (k n : ℕ) : weight k (n+1) ≤ (2:ℝ)^k * weight k n:= by
  unfold Grading.weight; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity) _ _; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]
lemma path_tariff (h : PowerPrice S B r C) : (smearedBlocks S B f).Tariff k (k+2+r+r) (meterLoss r k C f a) := by
  intro m n
  let l := k+2+r
  let L:= smearedBlocks S B f; let A:=L.op m n
  let D:= dollycoin a l f; have hD: 0≤D:=dolly_nonneg a l f
  apply le_of_mul_le_mul_right _ (weight_pos r m)
  calc weight (k+2) m * ‖A‖ * weight r m = weight l m * ‖A‖ := by unfold Grading.weight l; rw [pow_add]; ring
       _ ≤ D * ‖B.op m n‖ * weight l (n+1) := late_light S B f m n l
       _ ≤ D * (C*weight r m * weight r n) * ((2:ℝ)^l*weight l n) := by
           exact mul_le_mul (mul_le_mul_of_nonneg_left (h m n) hD) (next_le l n) (weight_pos _ _).le (mul_nonneg hD ((norm_nonneg _).trans (h m n)))
       _ = _ := by unfold meterLoss Grading.weight; change _=((2:ℝ)^l*C*D)*(((n+1:ℕ):ℝ)^(l+r))*_; rw [pow_add]; ring
lemma usableBlocks (p : PowerPaid S B) : (smearedBlocks S B f).Usable := by
  obtain ⟨r,C,h,t⟩:=p; exact fun k=> ⟨_,_,meter_nonneg r k C f h, path_tariff S B r k C f t⟩
end YM.SatinRegistration
