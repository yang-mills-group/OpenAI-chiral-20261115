import YM.SU5.Registration.Unpad
import YM.SU5.Same.DayBreak

/-!
# Unconditional prices on the domain, for the one-field vectors

An extra power payment lets us take the M4 heat limits even in the topology
of all the energy budgets. Unlike the operator-valued field estimates, this
step applies to the *given* `AtZeroHeat` without any operator growth premise.
We also keep the approach from the width-approximant kets at fixed extra
padding. This is in their genuine spectrum, not via real evolution just on a
new cyclic-field-word space. No norm bounds on the unsmeared vacuum column at
zero heat here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "G" => bands S
local notation "D" => radial S
local notation "T" => S.E
local notation "P" => cell S

/-- Heat maps even Hilbert inputs to the domain at strict positive heat. -/
def heatingWeight (s : ℝ≥0) (n : ℕ) := Real.exp (-(s:ℝ)*n)
lemma heating_count (k : ℕ) {s : ℝ≥0} (p : 0<s) : Summable (fun n=> Grading.weight k n*heatingWeight s n) := by
  have he : Summable (fun n:ℕ=> ((n+1:ℕ):ℝ)^k * heatingWeight s (n+1)) := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul k (show (0:ℝ)<s from p))
  refine (he.mul_right (Real.exp s)).congr (fun n=>?_); unfold Grading.weight heatingWeight; rw [mul_assoc,←Real.exp_add]; push_cast; ring_nf
lemma heating_band (s : ℝ≥0) (n : ℕ) : ‖P n * T s‖ ≤ heatingWeight s n := by
  refine Registers.fare ((Registers.box S.ℚmeasure (foldBand_meas n)).times (costT S s)) (Real.exp_nonneg _) fun p=>?_
  by_cases v:p∈foldBand a n
  · simp only [Pi.mul_apply,indicator_of_mem v,Pi.one_apply,one_mul,Complex.norm_real,Real.norm_of_nonneg (favorL _ _).1.le]
    exact Real.exp_monotone (mul_le_mul_of_nonpos_left (show (n:ℝ) ≤ timeOf a p from v.1) (neg_nonpos_of_nonneg s.property))
  simp only [Pi.mul_apply,indicator_of_notMem v,zero_mul,norm_zero]; exact Real.exp_nonneg _
lemma heat_domain (x : H) {s : ℝ≥0} (p : 0<s) : T s x ∈ radial S := by
  intro k; apply Summable.of_nonneg_of_le ((bands S).due_nonneg _ k) _ ((heating_count k p).mul_right ‖x‖)
  intro n; unfold Grading.due; rw [band,mul_assoc]; exact mul_le_mul_of_nonneg_left (((P n*T s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (heating_band S s n) (norm_nonneg _))) (weight_pos k n).le

abbrev freight (k : ℕ) (f : Test4) := (2:ℝ)^k * ((Finset.Iic (k,0)).sup (schwartzSeminormFamily ℝ E4 ℂ)) (onward f)
lemma pays_freight (f : Test4) (k : ℕ) (x : E4) : (1+‖x‖)^k * ‖onward f x‖ ≤ freight k f := by
  have he := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ) (m:=(k,0)) (le_refl k) (le_refl 0) (onward f) x; simp only [norm_iteratedFDeriv_zero] at he; exact he
lemma freight_nonneg (k : ℕ) (f : Test4) : 0 ≤ freight k f:=le_trans (b:=(1+‖(0:E4)‖)^k* ‖onward f 0‖) (by positivity) (pays_freight f k 0)

lemma band_collect (f : Test4) (k n : ℕ) : ‖P n * collect S f‖ ≤ freight k f / weight k n := by
  refine Registers.fare ((Registers.box S.ℚmeasure (foldBand_meas n)).times (collect_member S f)) (div_nonneg (freight_nonneg k f) (weight_pos k n).le) fun u=>?_
  by_cases h:u∈foldBand a n
  · simp only [Pi.mul_apply,indicator_of_mem h,Pi.one_apply,one_mul]; rw [le_div_iff₀ (weight_pos k n),mul_comm]; refine le_trans ?_ (pays_freight f k u)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold Grading.weight
    have hp:(n:ℝ) ≤ ‖u‖:= le_trans (show (n:ℝ) ≤ timeOf a u from h.1) (timeOf_bound u); gcongr; push_cast; linarith
  simp [h]; exact div_nonneg (freight_nonneg k f) (weight_pos k n).le
lemma collects (f : Test4) (k n : ℕ) (x : H) :
    (bands S).due (collect S f x) k n ≤ tariffW n*(freight (k+2) f*‖x‖) := by
  apply le_trans (b:= Grading.weight k n *(freight (k+2) f / Grading.weight (k+2) n * ‖x‖))
  · exact mul_le_mul_of_nonneg_left ((((P n* collect S f).le_opNorm x)).trans (mul_le_mul_of_nonneg_right (band_collect S f (k+2) n) (norm_nonneg _))) (weight_pos k n).le
  apply le_of_eq; unfold tariffW; rw [show Grading.weight (k+2) n=Grading.weight k n*Grading.weight 2 n from pow_add ..]; field_simp [(weight_pos k n).ne',(weight_pos 2 n).ne']
lemma collected (f : Test4) (x : H) : collect S f x ∈ D := fun k => (tariffW_summable.mul_right (freight (k+2) f*‖x‖)).of_nonneg_of_le ((bands S).due_nonneg _ k) (fun n=> collects S f k n x)

def gathers (f : Test4) : H →ₗ[ℂ] (radial S) := (collect S f).toLinearMap.codRestrict (radial S) (collected S f)
lemma gathers_price (k : ℕ) (f : Test4) (x : H) : (bands S).budget k (gathers S f x).1 ≤
    (∑' n, tariffW n)*(freight (k+2) f*‖x‖) := by
  refine ((rapid (gathers S f x).2 k).tsum_le_tsum (fun n=> collects S f k n x) (tariffW_summable.mul_right _)).trans_eq tsum_mul_right
lemma gather_approaches {ι : Type*} {l : Filter ι} (f : Test4) {X : ι→H} {x:H} (hx:Tendsto X l (𝓝 x)) :
    (bands S).Approaches l (fun i=> gathers S f (X i)) (gathers S f x) := by
  intro k; let p:= (∑' n, tariffW n)*freight (k+2) f
  refine squeeze_zero (fun _=> (bands S).budget_nonneg _ _) (fun i=> show _ ≤ p* ‖X i-x‖ from ?_) ?_
  · rw [show ((gathers S f) (X i)).1- (gathers S f x).1=(gathers S f (X i-x)).1 from by rw [map_sub]; rfl]; unfold p; rw [mul_assoc]; exact gathers_price S k f _
  simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hx).const_mul p

variable (X : ℝ→H)
open CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
variable (p : TemperedAtEdge H X) (u : SatinJets.Positive S X)
lemma wake_band (f : Test4) (n : ℕ) : P n (awake S X p f)=earnings S X n f:=by
  have he:= aSide S X p f
  rw [←(hasAwake S X p f).tsum_eq,(P n).map_tsum he,tsum_eq_single n]
  · exact (member S).1 (earnings_in S X n f)
  intro i hi
  exact (congrArg (P n) (((member S).1 (earnings_in S X i f)).symm)).trans ((bands S).project_other _ hi.symm)
lemma core_price (f : Test4) {r : ℕ} {C : ℝ} (z : ∀ n, ‖wing S X n‖ ≤ C*Grading.weight r n) (k n : ℕ) :
    (bands S).due (awake S X p f) k n ≤ tariffW n * (freight (k+r+2) f * C) := by
  unfold Grading.due; rw [band,wake_band]; let i:= k+r+2; let w:=wing S X n
  have hp:earnings S X n f= (P n*collect S f) w:= ((member S).1 (earnings_in S X n f)).symm
  rw [hp]
  refine le_trans (b:= weight k n*( freight i f /Grading.weight i n*(C*Grading.weight r n))) (mul_le_mul_of_nonneg_left (((P n*collect S f).le_opNorm w).trans (mul_le_mul (band_collect S f _ n) (z n) (norm_nonneg _) (div_nonneg (freight_nonneg ..) (weight_pos i n|>.le)))) (weight_pos k n|>.le)) (le_of_eq ?_)
  rw [show Grading.weight i n=Grading.weight k n*Grading.weight r n*Grading.weight 2 n from by unfold i Grading.weight; rw [pow_add,pow_add],tariffW]; dsimp only [i]; field_simp [(weight_pos k n).ne',(weight_pos r n).ne',(weight_pos 2 n).ne']
lemma wake_radial (f : Test4) : awake S X p f ∈ radial S:= by
  intro k; obtain ⟨m,C,hC,h⟩:= wing_grows S X p; exact (tariffW_summable.mul_right (freight (k+m+2) f*C)).of_nonneg_of_le ((bands S).due_nonneg _ k) (fun n=> core_price S X p f h k n)
def radialWake : Test4 →ₗ[ℂ] (radial S) := (awake S X p).toLinearMap.codRestrict (radial S) (wake_radial S X p)
include u
lemma radial_limit (f : Test4) : (bands S).Approaches (𝓝[>] (0:ℝ≥0)) (fun t=> gathers S f (X t)) (radialWake S X p f) := by
  let y:= radialWake S X p f
  let l:= 𝓝[>] (0:ℝ≥0)
  have he: (bands S).Approaches l (fun t=> y) y:= by intro k; simp_rw [sub_self,Grading.budget, Grading.due,map_zero,norm_zero,mul_zero,tsum_zero]; exact tendsto_const_nhds
  have h:= through_heat S l id (tendsto_id.mono_left (nhdsWithin_le_nhds (a:=(0:ℝ≥0)) (s:=Ioi 0))) he
  rw [stoveAt_zero] at h; intro k; refine (h k).congr' ((show ∀ᶠ t in l,0<t from self_mem_nhdsWithin).mono fun t v =>?_)
  change (bands S).budget k (T t (awake S X p f)-y.1) = (bands S).budget k (collect S f (X t)-y.1)
  rw [awake_on_axis S X p u t v]
end YM.SatinRegistration
