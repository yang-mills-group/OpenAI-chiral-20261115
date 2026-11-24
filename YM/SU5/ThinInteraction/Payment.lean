import YM.SU5.ThinInteraction.Bilateral
import SatinFixedContrastNovember4

/-! Thin interaction payment lemmas, optional supplement. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500

noncomputable section
namespace YM.SatinThin
open MeasureTheory Filter Spectral OS Semigroup TopologicalSpace Set
open scoped Topology InnerProductSpace ENNReal NNReal ComplexConjugate
open Six
open scoped BigOperators
section focus

/-- Signed moment parameter. opp=true: forward vector of the reflected mark; use -λ in the filter. -/
def moment (opp: Bool) (p : E4) : ℝ := if opp then -YM.time p else YM.time p
lemma moment_meas (opp : Bool) : Measurable (moment opp) := by
  cases opp; exact Mink.clock_cont.measurable; exact Mink.clock_cont.neg.measurable
variable {T : Set ℝ} {h : ℝ}
/-- In the PLUS field, shift **by -t**, and thus by t in the MINUS field. -/
def offset (opp : Bool) (t : Shop T h) : ℝ := if opp then t.val else -t.val
def whenFocus (opp : Bool) (t : Shop T h): ℝ≥0 := (h + offset opp t).toNNReal
lemma timing (opp : Bool) (t : Shop T h) : (whenFocus opp t:ℝ)=h+offset opp t := by
  unfold whenFocus; rcases t.prop.1 with ⟨a,b⟩; rw [Real.coe_toNNReal]; cases opp <;> simp only [offset,Bool.false_eq_true,↓reduceIte] <;> linarith
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
local notation "Q" => S.ℚmeasure
lemma zeroRep : (Q).Represents (0:E4→ℂ) 0 := by simpa using (Q).represents_one.sub (Q).represents_one
lemma repsStone (t : Shop T h) (opp:Bool):
    (Q).Represents (fun p:E4 => ((stone h t (moment opp p)):ℂ)) (S.E (whenFocus opp t)) := by
  apply (rep_heat S _).congr
  intro x
  filter_upwards [positive_energy S x] with p hp
  have he : 0 ≤ YM.time p := hp
  rw [fade]
  congr 1
  change Real.exp (- ((whenFocus opp t:ℝ) * YM.time p))=_
  rw [timing]
  cases opp <;> simp only [moment,Bool.false_eq_true,offset,stone, ↓reduceIte, abs_of_nonneg he, abs_neg] <;> congr 1 <;> ring

def focusing (opp : Bool) (c : Shop T h →₀ ℝ) : H.Op :=
   ∑ i∈c.support, ((c i:ℝ):ℂ) • S.E (whenFocus opp i)
lemma rep_sum {ι : Type*} (f : ι→ E4→ℂ) (g : ι→ H.Op) (s : Finset ι) (hfg : ∀ i,(Q).Represents (f i) (g i)):
    (Q).Represents (∑ i∈s,f i) (∑ i∈s,g i):= by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zeroRep S
  | @insert x s hx ih => rw [Finset.sum_insert hx,Finset.sum_insert hx]; exact (hfg x).add ih

def rays (c : Shop T h →₀ ℝ) (x : ℝ):ℝ:= ∑ i∈c.support, c i * stone h (i:ℝ) x
lemma represents_focus (opp : Bool) (c : Shop T h →₀ ℝ):
    (Q).Represents (fun p:E4 => ((rays c (moment opp p)):ℂ)) (focusing S opp c) := by
  let f (i : Shop T h) (p:E4):ℂ:= stone h i (moment opp p)
  have he : (fun p:E4 => ((rays c (moment opp p)):ℂ))= ∑ i∈c.support, ((c i:ℝ):ℂ) • f i := by
    ext p; unfold rays; push_cast; rw [Finset.sum_apply]; rfl
  rw [he,focusing]; exact rep_sum S _ _ _ (fun i => (repsStone S i opp).smul _)

private lemma approx_budget (μ : Measure ℝ) [IsFiniteMeasure μ] (c : Shop T h →₀ ℝ) :
    (fun x => ((∑ i∈c.support, c i • stone2 μ T h i : Lp ℝ 2 μ) x)) =ᵐ[μ] rays c := by
  let f (i: Shop T h) (x:ℝ) := c i * stone h i x
  have he (i) : (fun x=> ((c i • stone2 μ T h i : Lp ℝ 2 μ) x)) =ᵐ[μ] f i := by
    filter_upwards [Lp.coeFn_smul (c i) (stone2 μ T h i), (stone_mem2 μ i).coeFn_toLp] with x a b
    change stone2 μ T h i x = _ at b
    rw [a]; simp only [Pi.smul_apply]; rw [b]; rfl
  filter_upwards [Lp.coeFn_finsetSum c.support (fun i=> c i • stone2 μ T h i), (eventually_all_finset c.support).mpr (fun x _=> he x)] with x a b
  rw [a,Finset.sum_apply]; exact Finset.sum_congr rfl b
private lemma approx_sq (μ:Measure ℝ) [IsFiniteMeasure μ] {f:ℝ → ℝ} (hm : MemLp f 2 μ) (c : Shop T h →₀ ℝ):
    MemLp (fun x=> f x-rays c x) 2 μ ∧
      (∫ w, (f w-rays c w)^2 ∂μ) = ‖hm.toLp f-∑ i∈c.support, c i • stone2 μ T h i‖^2 := by
  let y := hm.toLp f-∑ i∈c.support, c i • stone2 μ T h i
  have he : (fun x=> y x) =ᵐ[μ] (fun x=> f x-rays c x) := by
    filter_upwards [Lp.coeFn_sub (hm.toLp f) (∑ i∈c.support, c i • stone2 μ T h i), hm.coeFn_toLp, approx_budget μ c] with x a b h
    unfold y; rw [a]; simp only [Pi.sub_apply]; exact congrArg₂ (·-·) b h
  refine ⟨(Lp.memLp y).ae_eq he, ?_⟩ -- .congr
  rw [←show inner ℝ y y = ‖y‖^2 from real_inner_self_eq_norm_sq _, L2.inner_def]; refine integral_congr_ae (he.mono (fun x h=> ?_))
  simp [h,pow_two]

/-- One focus purchase. No bound required on the costs of the coefficients. -/
lemma focusAll (ht : Dense T) (p : 0<h) (x : Bool→ H.space)
    (f : ℝ→ℝ) (F : Bool→H.Op) (hf : Measurable f) {A : ℝ} (e : ∀ i, ‖f i‖ ≤ A)
    (hr : ∀ b,(Q).Represents (fun p:E4 => ((f (moment b p)):ℂ)) (F b))
    {ε : ℝ} (u : 0<ε) : ∃ c:Shop T h→₀ℝ, ∀ b, ‖F b (x b) - focusing S b c (x b)‖ < ε := by
  let μ (b : Bool) := ((Q).diagonal (x b)).map (moment b)
  let ν := μ false + μ true
  haveI (b:Bool) : IsFiniteMeasure (μ b) := by unfold μ; infer_instance
  haveI : IsFiniteMeasure ν := by unfold ν; infer_instance
  have he : MemLp f 2 ν := MemLp.of_bound hf.aestronglyMeasurable A (ae_of_all _ e)
  obtain ⟨c,hc⟩ := stone_purchase ν ht p (he.toLp f) u
  let g (b:Bool) := focusing S b c
  let k (t:ℝ) := (f t-rays c t)^2; let q (b:Bool) := ‖F b (x b) - g b (x b)‖
  obtain ⟨hh,hx⟩ := approx_sq ν he c
  have hi : Integrable k ν := hh.integrable_sq
  have hi' (b:Bool) : Integrable k (μ b):= hi.mono_measure (by cases b; exact Measure.le_add_right (le_refl _); exact Measure.le_add_left (le_refl _))
  have hy (b:Bool) : q b ^ 2 = ∫ w,k w ∂μ b := by
    change ‖(F b-g b) (x b)‖^2=_
    rw [((hr b).sub (represents_focus S b c)).norm_sq (x b)]; unfold μ; rw [integral_map (moment_meas _).aemeasurable (hi' b).1]; simp only [Pi.sub_apply,←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,sq_abs,k]
  have hs:q false ^ 2 + q true ^ 2 < ε^2 := by
    rw [hy,hy,← integral_add_measure (hi' false) (hi' true)]; exact lt_of_eq_of_lt hx ((sq_lt_sq₀ (norm_nonneg _) u.le).mpr hc)
  exact ⟨c, fun b => (sq_lt_sq₀ (norm_nonneg _) u.le).mp (show q b ^ 2 < _ from by cases b <;> nlinarith only [hs,sq_nonneg (q false),sq_nonneg (q true)])⟩
end focus

section bands
open scoped BigOperators
open Set Classical
variable {T : Set ℝ} {h : ℝ}

/-- Set of physical energies paying the indicated scaled interval. -/
def cents (I : Set ℝ) (ρ : ℝ) : Set ℝ := (fun p:ℝ => ρ * p) ⁻¹' I
def band (I : Set ℝ) (ρ : ℝ) (m:ℕ) : Set ℝ := cents I ρ ∩ Set.Icc ((m:ℝ)+1) (m+2)
/-- Preimage from physical E4. -/
def by_time (A : Set ℝ) := YM.time ⁻¹' A
lemma cents_meas (I : Set ℝ) (p : MeasurableSet I) (ρ : ℝ): MeasurableSet (cents I ρ) :=
  (measurable_const_mul ρ) p -- type
lemma band_meas (I : Set ℝ) (p : MeasurableSet I) (ρ : ℝ) (m : ℕ) : MeasurableSet (band I ρ m):= (cents_meas I p ρ).inter measurableSet_Icc
lemma bymeas {A : Set ℝ} (h : MeasurableSet A) : MeasurableSet (by_time A):= Mink.clock_cont.measurable h
lemma band_pos {A : Set ℝ}{ρ : ℝ}{m : ℕ} : band A ρ m ⊆ Set.Ioi 0 := fun x p => by
  have hm := p.2.1; have he : 0 ≤ (m:ℝ) := Nat.cast_nonneg _; exact lt_of_lt_of_le (by linarith) hm

def bill (A : Set ℝ) (α : ℝ) (w : ℝ≥0): ℝ→ℝ := A.indicator (fun x : ℝ => α*Real.exp (-((w:ℝ)*x)))
lemma bill_bound {A : Set ℝ} (p : A ⊆ Set.Ioi 0) (α : ℝ) (w : ℝ≥0) (x : ℝ): ‖bill A α w x‖≤ ‖α‖:= by
  unfold bill; by_cases h:x∈A
  · rw [indicator_of_mem h,norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg w.property (show 0<x from p h).le)))
  rw [indicator_of_notMem h,norm_zero]; exact norm_nonneg _
variable {H : Hilbert} (S : OS.Semigroup H timeAxis)
local notation "Q" => S.ℚmeasure
variable (A : Set ℝ)(B : MeasurableSet A)(α : ℝ)(w : ℝ≥0)
def enjoy (opp:Bool) : H.Op := if opp then 0 else ((α:ℝ):ℂ) • ((Q).region (by_time A)* S.E w)
include B
lemma realizes_bill (u : A ⊆ Set.Ioi 0) (b:Bool) : (Q).Represents
    (fun p:E4 => ((bill A α w (moment b p)):ℂ)) (enjoy S A α w b) := by
  cases b
  · refine (((rep_heat S w).indicator (bymeas B)).smul (α:ℂ)).congr ?_
    intro x; filter_upwards with p
    by_cases h : YM.time p ∈ A
    · rw [Pi.smul_apply, smul_eq_mul, indicator_of_mem (show p∈by_time A from h)]; simp only [bill,moment,Bool.false_eq_true,↓reduceIte]; rw [indicator_of_mem h]; simp [fade,Balloon.tinct,YM.time]
    rw [Pi.smul_apply,indicator_of_notMem (show p∉by_time A from h), smul_zero]; simp only [bill,moment,Bool.false_eq_true,↓reduceIte]; rw [indicator_of_notMem h, Complex.ofReal_zero]
  refine (zeroRep S).congr ?_
  intro x; filter_upwards [positive_energy S x] with p hp
  have ht : 0≤YM.time p:=hp
  rw [Pi.zero_apply]; unfold bill; rw [indicator_of_notMem (a:=moment true p) (fun e => not_lt_of_ge (neg_nonpos.mpr ht) (u e)), Complex.ofReal_zero]

lemma enjoy_both (x : Bool → H.space) (u : A ⊆ Set.Ioi 0) (t : Dense T) (p : 0 < h) (δ : ℝ) (q : 0<δ):
    ∃ c : Shop T h →₀ ℝ, ∀ b, ‖enjoy S A α w b (x b) - focusing S b c (x b)‖ < δ :=
  focusAll S t p x (bill A α w) (enjoy S A α w) (by unfold bill; fun_prop) (bill_bound u α w)
    (realizes_bill S A B α w u) q

omit B
lemma live_rep {f:E4→ℂ}{T:H.Op}(h:(Q).Represents f T) {V : Set E4} (u : MeasurableSet V) (p: ∀ x∈V,f x≠0) (x:H) (ht: (Q).region V x ≠ 0):
    (Q).region V (T x) ≠ 0 := by
  intro hc
  let μ := (Q).diagonal x; let y:= V.indicator f; let W := (Q).region V * T; let g (w:E4):= ‖y w‖^2
  have hW := h.indicator u; change (Q).Represents y W at hW; change W x=0 at hc
  have hi : Integrable g μ := by
    have he := hW.square.admissible.integrable x
    exact Integrable.re he
  have hz : ∫ p, g p ∂μ = 0 := by rw [← hW.norm_sq x, hc]; simp
  have he := (integral_eq_zero_iff_of_nonneg (f:=g) (fun a=> sq_nonneg _) hi).1 hz
  refine ht (((Q).null_pair u x).1 ?_)
  have hx : ∀ᵐ t∂μ, t∉ V := he.mono fun a ha hv => (pow_ne_zero 2
      (norm_ne_zero_iff.mpr (show y a≠0 from by rw [show y= V.indicator f from rfl, indicator_of_mem hv]; exact p a hv))) ha
  simpa [ae_iff] using hx

lemma leave_zero (a w:ℝ≥0) (e:0<w) (A:Set E4) (u:MeasurableSet A) (h:∀ i∈A,0<YM.time i) (x:H) (ht: (Q).region A x ≠ 0):
    (Q).region A (S.E a (x - S.E w x)) ≠ 0:= by
  refine live_rep S ((rep_heat S a).mul ((Q).represents_one.sub (rep_heat S w))) u (fun i g => ?_) x ht
  change fade a i * ((1:ℂ)-fade w i) ≠ 0
  refine mul_ne_zero ?_ (sub_ne_zero.mpr ?_)
  · simp only [fade,Balloon.tinct,ne_eq,Complex.ofReal_eq_zero]
    exact Real.exp_ne_zero _
  apply Ne.symm
  have he : (w:ℝ)>0:= by exact_mod_cast e
  unfold fade Balloon.tinct; rw [ne_eq, Complex.ofReal_eq_one]
  exact (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos he (h i g)))).ne
end bands
end YM.SatinThin

#print axioms YM.SatinThin.leave_zero
#print axioms YM.SatinThin.enjoy_both
