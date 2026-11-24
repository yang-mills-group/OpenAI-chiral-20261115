import YM.CF.BProof.Law.Move
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/- finite Z and gaussian tail. z is |v|^2 cut (positive). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release.Day
open Function MeasureTheory Finset Filter Set
open scoped BigOperators Topology Classical ENNReal
variable {I:Type}[Fintype I]
variable (p z u : ℝ)
variable (x : I→ ℝ)
def ar (x:I→ ℝ) := ∑ i,x i^2
def gar (x:I→ ℝ) := Real.exp (-p*ar x)
def pit (z:ℝ): Set (I→ℝ) := {x|ar x≤z}
def ore := (pit z).indicator (gar (I:=I) (1/2))
def Z (I:Type)[Fintype I] := ∫ x:I→ℝ,ore z x
@[fun_prop] lemma ar_c : Continuous (ar (I:=I)):= by unfold ar; fun_prop
@[fun_prop] lemma gar_c : Measurable (gar (I:=I) p):=Real.measurable_exp.comp (measurable_const.mul ar_c.measurable) -- tune
lemma pit_c : MeasurableSet (pit (I:=I) z):= measurableSet_le ar_c.measurable measurable_const
@[fun_prop] lemma ore_c : Measurable (ore (I:=I) z):= (gar_c _).indicator (pit_c z)
lemma ar_pos : 0≤ ar x := sum_nonneg fun _ _=> sq_nonneg _
lemma ore_0 : 0≤ ore z x := indicator_nonneg (fun y _=> (Real.exp_pos _).le) x
lemma ridden (hp:0<p) : Integrable (gar (I:=I) p):=by
 rw [show gar (I:=I) p=(fun x:I→ℝ=>∏ i,Real.exp (-p*x i^2)) from funext fun x=> by unfold gar ar; rw [mul_sum,Real.exp_sum]]; exact Integrable.fintype_prod (ι:=I) (fun i=>integrable_exp_neg_mul_sq hp) -- tune
lemma price (I:Type)[Fintype I] : Integrable (ore (I:=I) z):=(ridden _ (by norm_num)).indicator (pit_c z)
lemma filled (I:Type)[Fintype I](v:0<z) : 0<Z z I := by
 apply (integral_pos_iff_support_of_nonneg (ore_0 z) (price z I)).2; let S:= ar (I:=I) ⁻¹' Iio (α:=ℝ) z
 have hh:IsOpen (S:Set (I→ℝ)):=isOpen_Iio.preimage ar_c
 refine lt_of_lt_of_le (hh.measure_pos volume ⟨0,?_⟩) (measure_mono (show S⊆Function.support _ from ?_))
 · change ar (0:I→ℝ)<z; simpa [ar]
 exact fun y hy=> by rw [Function.mem_support,ore,indicator_of_mem (show y∈pit z from le_of_lt (show ar y<z from hy))]; exact (Real.exp_pos _).ne'
def total (I:Type)[Fintype I] := ∫ x:I→ℝ,gar p x
lemma ground (I:Type)[Fintype I](hu:u≤z): Z u I≤Z z I := by apply integral_mono (price ..) (price ..); intro x; by_cases h:x∈pit u; unfold ore; rw [indicator_of_mem h,indicator_of_mem (show x∈pit z from le_trans h hu)]; rw [ore,indicator_of_notMem h]; exact ore_0 z x
lemma ceiling (I:Type)[Fintype I] : Z z I≤total (1/2) I := by apply integral_mono (price ..) (ridden _ (by norm_num)); intro x; by_cases h:x∈pit z; exact Eq.le (Set.indicator_of_mem h _); unfold ore; rw [indicator_of_notMem h]; exact (Real.exp_pos _).le

def ticket (z:ℝ) (x:I→ℝ):= (Z z I)⁻¹*ore z x
def mark (z:ℝ) (I:Type)[Fintype I] := volume.withDensity (fun x:I→ ℝ=> ENNReal.ofReal (ticket z x))
@[fun_prop] lemma ticket_m : Measurable (ticket (I:=I) z):= measurable_const.mul (ore_c z)
lemma ticket_pay : Integrable (ticket (I:=I) z) := (price ..).const_mul _
lemma ticket_pos (v:0<z) : 0≤ ticket z x:= mul_nonneg (inv_nonneg.mpr (filled z I v).le) (ore_0 ..)
lemma ticket_on (h:x∈pit z) (v:0<z): 0<ticket z x:=by unfold ticket ore; rw [indicator_of_mem h]; exact mul_pos (inv_pos.mpr (filled z I v)) (Real.exp_pos _)
lemma ticket_off (h:x∉pit z): ticket z x=0:=by unfold ticket ore; rw [indicator_of_notMem h,mul_zero]
lemma fee {S:Set (I→ ℝ)}(v:0<z)(h:MeasurableSet S) : mark z I S= ENNReal.ofReal (∫ x in S,ticket z x):=by
 unfold mark; rw [withDensity_apply _ h, ofReal_integral_eq_lintegral_ofReal (ticket_pay (I:=I) z).integrableOn (Eventually.of_forall fun i=> ticket_pos z i v)]
lemma prob (I:Type)[Fintype I](v:0<z): IsProbabilityMeasure (mark z I):=by
 refine ⟨?_⟩; rw [fee z v MeasurableSet.univ, setIntegral_univ]; unfold ticket; rw [integral_const_mul, ← Z,inv_mul_cancel₀ (filled z I v).ne',ENNReal.ofReal_one] -- tune fold
lemma dwelt (I:Type)[Fintype I]: ∀ᵐ x ∂mark z I,x∈pit z:=by
 apply (ae_withDensity_iff (ticket_m z).ennreal_ofReal).2; apply Eventually.of_forall; intro x h; by_contra H; apply h; rw [ticket_off z x H,ENNReal.ofReal_zero] -- tune
lemma city (I J:Type)[Fintype I][Fintype J](v:0<z): ∀ᵐ x∂Measure.pi (fun _:J=>mark z I),∀ i,x i∈ pit z:=by
 haveI:=prob z I v; apply ae_all_iff.mpr; intro i; exact (Measure.quasiMeasurePreserving_eval (μ:=fun _:J=>mark z I) i).tendsto_ae (dwelt z I)
def peak (u:ℝ): Set (I→ℝ) := {x| u≤ar x}
def tip (I:Type)[Fintype I] (u:ℝ) := (Z 1 I)⁻¹*total (1/4) I * Real.exp (-u/4)
lemma peak_m : MeasurableSet (peak (I:=I) u):= measurableSet_le measurable_const ar_c.measurable
lemma total_0 : 0≤total p I:= integral_nonneg fun _=> (Real.exp_pos _).le
lemma tariff (u:ℝ)(v:1≤z): (mark z I).real (peak u)≤ tip I u:=by
 let r:=peak (I:=I) u; have hg:0<z:=one_pos.trans_le v; let a:= Z (1:ℝ) I; let b:= Z z I; have ha:0<a:= filled 1 I one_pos; have hb:a≤b:= ground z 1 I v; have hc:0≤ Real.exp (-u/4):=(Real.exp_pos _).le
 rw [measureReal_def,fee z hg (peak_m u),ENNReal.toReal_ofReal (integral_nonneg fun x=> ticket_pos z x hg), ← integral_indicator (peak_m u)]
 have hy:= (ridden (I:=I) (1/4) (by norm_num)).const_mul (a⁻¹*Real.exp (-u/4))
 apply le_trans (integral_mono ((ticket_pay z).indicator (peak_m u)) hy ?_) ?_ -- tune
 swap
 · rw [integral_const_mul]; exact le_of_eq (by unfold tip; change a⁻¹*_*total _ I=a⁻¹*_*_; ring)
 intro x; by_cases h:x∈r ∧ x∈pit z
 · change r.indicator _ _ ≤_; rw [indicator_of_mem h.1]; unfold ticket ore; rw [indicator_of_mem h.2]; dsimp only; rw [mul_assoc]; apply mul_le_mul (inv_anti₀ ha hb) _ (Real.exp_pos _).le (inv_pos.mpr ha).le; unfold gar; rw [←Real.exp_add,Real.exp_le_exp]; linarith only [show u ≤ ar x from h.1]
 apply le_trans (b:=0) _ (by have h:=Real.exp_pos (-(1/4)*ar x); exact mul_nonneg (mul_nonneg (inv_pos.mpr ha).le hc) h.le); change r.indicator _ _≤_; rcases not_and_or.mp h with h|h; rw [indicator_of_notMem h]; by_cases k:x∈r; rw [indicator_of_mem k,ticket_off z x h]; rw [indicator_of_notMem k]
end YM.CF.BProof.Release.Day
