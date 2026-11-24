/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Budget
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Filter Function Set Asymptotics
open scoped Topology BigOperators NNReal ENNReal ContDiff

def fuelAllRC (v : ℝ) (n : ℝ≥0) := Real.exp (n*v)
lemma fuel_posAllRC (v n) : 0 < fuelAllRC v n := Real.exp_pos _
lemma fuel0AllRC (n) : fuelAllRC 0 n=1 := by simp [fuelAllRC]
lemma fuel_negAllRC (v n) : fuelAllRC (-v) n=(fuelAllRC v n)⁻¹ := by simp [fuelAllRC, Real.exp_neg]
lemma fuel_mulAllRC (v w n) : fuelAllRC v n*fuelAllRC w n=fuelAllRC (v+w) n := by rw [fuelAllRC,fuelAllRC,← Real.exp_add,← mul_add]; rfl
lemma fuel_rateAllRC (v n) (k : ℕ) : fuelAllRC v n^k=fuelAllRC (v*k) n := by
  induction k with
  | zero => simp [fuel0AllRC]
  | succ k ih => rw [pow_succ,ih,fuel_mulAllRC,Nat.cast_add,Nat.cast_one,mul_add,mul_one]
lemma fuel_leAllRC {v w} (h : v≤w) (n) : fuelAllRC v n ≤ fuelAllRC w n := Real.exp_le_exp.mpr (by gcongr)
lemma fuel_growsAllRC {v} (h : 0<v) : Tendsto (fuelAllRC v) atTop atTop := Real.tendsto_exp_atTop.comp ((NNReal.tendsto_coe_atTop.mpr (tendsto_id (x:=atTop))).atTop_mul_const h)
lemma fuel_fallsAllRC {v} (h : v<0) : Tendsto (fuelAllRC v) atTop (𝓝 0) := by
  have he := fuel_growsAllRC (neg_pos.mpr h) |>.inv_tendsto_atTop
  refine he.congr (fun i => ?_); rw [Pi.inv_apply,fuel_negAllRC,inv_inv]
lemma biggerAllRC {a b : ℝ} (h : a<b) (C : ℝ) : ∀ᶠ i : ℝ≥0 in atTop, fuelAllRC a i*C ≤ fuelAllRC b i := by
  filter_upwards [(fuel_growsAllRC (sub_pos.mpr h)).eventually (eventually_ge_atTop C)] with i hi
  exact (mul_le_mul_of_nonneg_left hi (fuel_posAllRC a i).le).trans_eq (by rw [fuel_mulAllRC,add_sub_cancel])

section
variable {X : Type*} [SeminormedAddCommGroup X]
def BudgetAllRC (a : ℝ) (f : ℝ≥0 → X) := ∃ C : ℝ,0≤C ∧ ∀ᶠ i : ℝ≥0 in atTop, ‖f i‖ ≤ C*fuelAllRC a i
variable {f g : ℝ≥0→X} {x y : ℝ}
lemma BudgetAllRC.rise (h : BudgetAllRC x f) (he : x≤y) : BudgetAllRC y f := by
  obtain ⟨C,hC,h⟩ := h; exact ⟨C,hC,h.mono fun i hi => hi.trans (mul_le_mul_of_nonneg_left (fuel_leAllRC he _) hC)⟩
lemma BudgetAllRC.add (h : BudgetAllRC x f) (t : BudgetAllRC x g) : BudgetAllRC x (fun i => f i+g i) := by
  obtain ⟨C,hC,h⟩ := h; obtain ⟨D,hD,t⟩ := t; refine ⟨C+D,add_nonneg hC hD,?_⟩
  filter_upwards [h,t] with i hi hk; exact (norm_add_le ..).trans ((add_le_add hi hk).trans_eq (add_mul ..).symm)
lemma BudgetAllRC.neg (h : BudgetAllRC x f) : BudgetAllRC x (fun i => -f i) := by
  obtain ⟨C,hC,h⟩ := h; exact ⟨C,hC,by simpa using h⟩
lemma BudgetAllRC.sub (h : BudgetAllRC x f) (t : BudgetAllRC x g) : BudgetAllRC x (fun i => f i-g i) := by
  simp_rw [sub_eq_add_neg]; exact h.add t.neg
lemma constant_budgetAllRC (w : X) : BudgetAllRC 0 (fun _ => w) := ⟨‖w‖,norm_nonneg _,Eventually.of_forall fun i => by simp [fuel0AllRC]⟩
lemma no_budgetAllRC (v : ℝ) : BudgetAllRC v (fun _ => (0:X)) := ⟨0,le_rfl,by simp⟩
lemma BudgetAllRC.reduce {Y : Type*} [SeminormedAddCommGroup Y] {F : ℝ≥0→Y} (h : BudgetAllRC x f) (hh : ∀ᶠ n in atTop, ‖F n‖ ≤ ‖f n‖) : BudgetAllRC x F := by
  obtain ⟨C,hC,h⟩ := h; refine ⟨C,hC,?_⟩
  filter_upwards [hh,h] with i hi hh; exact hi.trans hh
lemma BudgetAllRC.limits (h : BudgetAllRC x f) (hx : x<0) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _)) h ?_
  simpa using (fuel_fallsAllRC hx).const_mul C
lemma BudgetAllRC.same (h : BudgetAllRC x f) (hh : f=ᶠ[atTop] g) : BudgetAllRC x g := h.reduce (hh.mono fun _ hi => Eq.le (congr_arg norm hi).symm)
lemma budget_sumAllRC {ι : Type*} (s : Finset ι) (F : ι → ℝ≥0 → X) (a) (h : ∀ i∈s,BudgetAllRC a (F i)) : BudgetAllRC a (fun n => ∑ i∈s,F i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact no_budgetAllRC _
  | @insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun _ v => h _ (by simp [v]))
end
variable {x y : ℝ}
lemma BudgetAllRC.priced {X : Type*} [SeminormedAddCommGroup X] {F : ℝ≥0 → X} {f : ℝ≥0 → ℝ}
    (h : BudgetAllRC x f) (hh : ∀ᶠ i in atTop, ‖F i‖ ≤ f i) : BudgetAllRC x F := h.reduce (hh.mono fun _ hi => hi.trans (le_abs_self _))
lemma BudgetAllRC.signed {f g : ℝ≥0→ℝ} (h : BudgetAllRC x f) (hg : ∀ᶠ i in atTop, 0 ≤ g i) (hh : ∀ᶠ i in atTop, g i≤f i) : BudgetAllRC x g := by
  apply h.priced; filter_upwards [hg,hh] with i hi he; simpa [Real.norm_of_nonneg hi] using he
lemma BudgetAllRC.prod {X : Type*} [SeminormedRing X] {f g : ℝ≥0 → X} (h : BudgetAllRC x f) (l : BudgetAllRC y g) : BudgetAllRC (x+y) (fun n => f n*g n) := by
  obtain ⟨C,hC,h⟩ := h; obtain ⟨D,hD,l⟩ := l
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [h,l] with n hx hy
  refine (norm_mul_le ..).trans ((mul_le_mul hx hy (norm_nonneg _) (hx.trans' (norm_nonneg _))) |>.trans_eq ?_)
  rw [← fuel_mulAllRC]; ring
lemma BudgetAllRC.times {X : Type*} [SeminormedRing X] {f : ℝ≥0 → X} (h : BudgetAllRC x f) (c : X) : BudgetAllRC x (fun n => c*f n) := by
  simpa only [zero_add] using (constant_budgetAllRC c).prod h
lemma BudgetAllRC.pow {f : ℝ≥0 → ℝ} (h : BudgetAllRC x f) (n : ℕ) : BudgetAllRC (x*n) (fun i => f i^n) := by
  induction n with
  | zero => simp_rw [pow_zero, Nat.cast_zero,mul_zero]; exact constant_budgetAllRC _
  | succ n ih => simp_rw [pow_succ,Nat.cast_add,Nat.cast_one,mul_add,mul_one]; exact ih.prod h
lemma budget_fuelAllRC (a) : BudgetAllRC a (fuelAllRC a) := ⟨1,zero_le_one,Eventually.of_forall fun i => by simp [abs_of_pos (fuel_posAllRC ..)]⟩
lemma budget_invAllRC (a) : BudgetAllRC (-a) (fun i => (fuelAllRC a i)⁻¹) := by simp_rw [← fuel_negAllRC]; exact budget_fuelAllRC _
end YM.NSF.Outer
