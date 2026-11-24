/- This file incorporates modified third-party source. See the source attributions in notices/. -/ -- Adapted from submitted project YM.Next.ROTATIONS and the indicated GaugeFieldConstruction/M modules, all-width (NONSEQUENCE) estimates
import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Charge
import GaugeFieldConstruction.CrystalGainsVU
/-! # Full-width companion to EXP budget -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Set Function Filter MeasureTheory Measure Row Boundary Probe OS Word Nodes
open scoped Topology NNReal ENNReal ContDiff BigOperators

def billAllRC (x n) (f : Profile) := width (fuelAllRC x n) f
def mailsAllRC (w : Axis → ℝ) (f : Grouping) (n : ℝ≥0) (i : Axis) := billAllRC (w i) n (f i)
lemma mail_roomAllRC {x a : ℝ} (h : x<a) (f : Profile) (hf : Ends f) : ∀ᶠ n in atTop, Room (billAllRC x n f) (fuelAllRC a n) := by
  obtain ⟨s,hs⟩ := hf.room
  filter_upwards [biggerAllRC h s] with i hi
  exact (hs.grow _ (fuel_posAllRC ..)).inc hi
lemma bill_plusAllRC {f : Profile} (h : Plus f) (x n) : Plus (billAllRC x n f) := h.tall _ (fuel_posAllRC ..).le
lemma bill_cashAllRC (x n) (f : Profile) (K : ℝ) (hx : -K ≤ x) (v) :
    ‖billAllRC x n f v‖ ≤ (SchwartzMap.seminorm ℝ 0 0 f)*fuelAllRC K n := by
  rw [billAllRC,width_at,norm_mul,norm_inv,Real.norm_of_nonneg (fuel_posAllRC ..).le,← fuel_negAllRC,mul_comm]
  refine mul_le_mul (f.norm_le_seminorm ℝ _) (fuel_leAllRC ?_ n) (fuel_posAllRC _ n).le (apply_nonneg _ _)
  linarith
lemma sum_cashAllRC (w : Axis→ℝ) (f : Grouping) (K n) (R : Finset Axis) (h : ∀ i∈R,-K≤w i) (p : E4) :
    ‖crop R (mailsAllRC w f n) p‖≤ (∏ i∈R,SchwartzMap.seminorm ℝ 0 0 (f i))*fuelAllRC (K*R.card) n := by
  rw [crop, norm_prod,← fuel_rateAllRC,← Finset.prod_const (s:=R)]
  rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => bill_cashAllRC _ _ _ K (h i hi) _

lemma credit_budgetAllRC (m j k : ℕ) (a : ℝ) (f : Profile) (x : ℝ) (d : ℝ) : BudgetAllRC ( (x-d)*(2*k:ℕ))
    (fun n => credits m j k (a*fuelAllRC d n) (billAllRC x n f)) := by
  let z := 2*k
  have hz : BudgetAllRC ((x+ -d)*z) (fun n => (fuelAllRC x n*(fuelAllRC d n)⁻¹)^z*tally z f) := by
    simp_rw [mul_comm _ (tally z f)]
    exact (((budget_fuelAllRC x).prod (budget_invAllRC d)).pow z).times _
  have hh := hz.times ((Nodes.coeff m j).coeff k * a⁻¹^z)
  rw [← sub_eq_add_neg] at hh
  refine hh.same (Eventually.of_forall fun i => ?_)
  dsimp only [credits,billAllRC]; rw [tally_width z _ (fuel_posAllRC ..),mul_pow,mul_inv,mul_pow]; ring
lemma paid_billAllRC (m : ℕ) (s : ℝ) (hs : 1≤s) (x d : ℝ) (hx : x≤d) (f : Profile) :
    ∃ g : Profile, Far g ∧ Plus g ∧ Reflects false g ∧ ∀ᶠ n in atTop,
      ∀ p : ℝ, ‖bake m (s*fuelAllRC d n) (billAllRC x n f) p‖ ≤ billAllRC d n g p := by
  have hf (j k : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ n in atTop, ‖credits m j k (s*fuelAllRC d n) (billAllRC x n f)‖ ≤ C := by
    obtain ⟨C,hC,h⟩ := (credit_budgetAllRC m j k s f x d).rise (y:=0) (by
      apply mul_nonpos_of_nonpos_of_nonneg (sub_nonpos_of_le hx); positivity)
    exact ⟨C,hC,by simpa only [fuel0AllRC,mul_one] using h⟩
  choose C hC h using hf
  let G j k := width s (menu j k)
  let g : Profile := ∑ j∈Finset.range m,∑ k∈dish m j,C j k • G j k
  have ht j k : Plus (G j k) := (menu_plus j k).tall _ (show 0≤s by linarith)
  refine ⟨g,Far.sum _ (fun j _ => Far.sum _ (fun k _ => ((menu_far j k).width _).scale _)),Plus.sum _ (fun j _ => Plus.sum _ (fun k _ => (ht j k).scale _ (hC ..))),
    Reflects.sum _ (fun j _ => Reflects.sum _ (fun k _ => ((menu_even j k).tall _).scale _)),?_⟩
  filter_upwards [(eventually_all_finset (Finset.range m)).mpr fun j hj => (eventually_all_finset _).mpr fun k (_ : k∈dish m j) => h j k] with i h p
  simp only [bake,board,billAllRC,g,_root_.sum_apply,_root_.map_sum, map_smul,_root_.smul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_smul, show width (s*fuelAllRC d i) (menu j k)=width (fuelAllRC d i) (G j k) by rw [mul_comm,width_mul],
    Real.norm_of_nonneg ((ht j k).tall (fuelAllRC d i) (fuel_posAllRC ..).le p)]
  exact mul_le_mul_of_nonneg_right (h j hj k hk) (bill_plusAllRC (ht j k) _ _ p)

lemma far_gainAllRC (x : ℝ) (hx : 0≤x) (k : ℕ) (f : Profile) (hf : Far f) : ∃ C : ℝ,0≤C ∧
    ∀ n : ℝ≥0, ∀ u : ℝ, ‖billAllRC x n f u‖ ≤ C*fuelAllRC (-x*(2*k:ℕ)) n*‖u‖^(2*k) := by
  obtain ⟨r,hr,h⟩ := Metric.mem_nhds_iff.mp hf.2
  let Q := SchwartzMap.seminorm ℝ 0 0 f
  have hQ : 0 ≤ Q := apply_nonneg _ _
  let D := Q*r⁻¹^(2*k)
  have hD : 0 ≤ D := mul_nonneg hQ (pow_nonneg (inv_pos.mpr hr).le _)
  refine ⟨D,hD,fun i u => ?_⟩
  let w := fuelAllRC x i
  have hw : 1 ≤ w := by simpa only [fuel0AllRC] using fuel_leAllRC hx i
  rw [show fuelAllRC (-x*(2*k:ℕ)) i=((fuelAllRC x i)⁻¹)^(2*k) by rw [← fuel_rateAllRC, fuel_negAllRC]]
  rw [billAllRC,width_at]; by_cases he : r ≤ ‖u/w‖
  · have hy : D*r^(2*k) ≤ D*‖u/w‖^(2*k) := by gcongr
    have ht : D*r^(2*k)=Q := by dsimp only [D]; rw [inv_pow]; field_simp
    rw [ht,norm_div,Real.norm_of_nonneg (show 0 ≤ w from (fuel_posAllRC x i).le),div_pow,div_eq_mul_inv] at hy
    rw [norm_mul,norm_inv,Real.norm_of_nonneg (fuel_posAllRC ..).le]; calc
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hw)
      _ ≤ _ := (f.norm_le_seminorm ℝ _).trans (hy.trans_eq ?_)
    dsimp only [w]; rw [inv_pow]; ring
  have hx : f (u/w)=0 := h (Metric.mem_ball.mpr (by simpa using lt_of_not_ge he))
  change ‖w⁻¹*f (u/w)‖ ≤ _
  rw [hx,mul_zero,norm_zero]; positivity

variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} (V : Chamber S i)

/-- Alternative cost with any high transverse axis moment. `z` turned into cap
before paying its band. -/
lemma far_payAllRC (A : Weight L) (h : ℝ≥0 → Profile) (Q : Finset Axis) (f : Grouping) (w : Axis → ℝ)
    (hs : ∀ᶠ n in atTop, ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i (h n) p) (K : ℝ)
    (hj : ∀ j∈Q, -K ≤ w j) (j : Axis) (hi : j∈Q) (he : j≠i) (k : ℕ) (a : ℝ)
    (hp : ∀ᶠ n in atTop, Integrable (fun p : E4 => Reel i (h n) p * ‖p j‖^(2*k)) (ν V A))
    (ht : BudgetAllRC a (fun n => ∫ p : E4, Reel i (h n) p * ‖p j‖^(2*k) ∂ν V A))
    (g : Profile) (hg : Far g) (u : ℝ) (hu : 0≤u) :
    BudgetAllRC (-u*(2*k:ℕ)+K*((Q.erase i).erase j).card+a)
      (fun n => pay (ν V A) i Q (h n) (update (mailsAllRC w f n) j (billAllRC u n g))) := by
  obtain ⟨C,hC,hG⟩ := far_gainAllRC u hu k g hg
  let x : ℝ := -u*(2*k:ℕ)
  let T := (Q.erase i).erase j
  let M := ∏ l∈T, SchwartzMap.seminorm ℝ 0 0 (f l)
  let y := K*T.card
  apply ((((budget_fuelAllRC x).times C).prod ((budget_fuelAllRC y).times M)).prod ht).priced
  filter_upwards [hp,hs] with n hx hn
  unfold pay
  let μ := ν V A
  let R (p : E4) := Reel i (h n) p * ‖p j‖^(2*k)
  let W := (C*fuelAllRC x n)*(M*fuelAllRC y n)
  change _ ≤ W * integral μ R
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hx.const_mul W) ?_
  filter_upwards [before V A] with p hp
  rw [crop_cons (Q.erase i) _ j _ _ (Finset.mem_erase.mpr ⟨he,hi⟩),norm_mul,norm_mul,Real.norm_of_nonneg (hn p hp)]
  have hb : ‖crop T (mailsAllRC w f n) p‖ ≤ M*fuelAllRC y n := sum_cashAllRC w f K n T (fun i hi => hj i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))) p
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (hG n _) hb (norm_nonneg _) ((hG n _).trans' (norm_nonneg _))) (hn p hp)) (le_of_eq ?_)
  dsimp only [W,x,R]; ring
lemma done_payAllRC (A : Weight L) (h : ℝ≥0 → Profile) (Q : Finset Axis) (f : Grouping) (w : Axis → ℝ)
    (hs : ∀ᶠ n in atTop, ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i (h n) p)
    (hj : ∀ j∈Q,0≤w j) (a : ℝ) (hp : ∀ᶠ n in atTop, Integrable (Reel i (h n)) (ν V A))
    (ht : BudgetAllRC a (fun n => ∫ p : E4, Reel i (h n) p ∂ν V A)) :
    BudgetAllRC a (fun n => pay (ν V A) i Q (h n) (mailsAllRC w f n)) := by
  let T := Q.erase i
  let M := ∏ l∈T, SchwartzMap.seminorm ℝ 0 0 (f l)
  apply (ht.times M).priced
  filter_upwards [hp,hs] with n hx hn
  unfold pay
  change _ ≤ M * integral (ν V A) (Reel i (h n))
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hx.const_mul M) ?_
  filter_upwards [before V A] with p hp
  rw [norm_mul, Real.norm_of_nonneg (hn p hp),mul_comm M]
  refine mul_le_mul_of_nonneg_left ?_ (hn p hp)
  have h : ∀ j∈T,-(0:ℝ)≤ w j := by simp_rw [neg_zero]; exact fun j h => hj j (Finset.mem_of_mem_erase h)
  simpa only [zero_mul,fuel0AllRC,mul_one] using sum_cashAllRC w f 0 n T h p
abbrev lampsAllRC (m : ℕ) (x d a : ℝ) (f : Profile) (n : ℝ≥0) := Resid m (a*fuelAllRC d n) (billAllRC x n f)
lemma lamp_signsAllRC (m : ℕ) (x d a : ℝ) (f : Profile) (hf : Ends f) (hp : Plus f) (n)
    (ha : 0<a) (hh : Room (billAllRC x n f) (a*fuelAllRC d n)) (i) (p : E4) (hi : 0 ≤ p i) :
    0 ≤ Reel i (lampsAllRC m x d a f n) p := lamp_sign m (a*fuelAllRC d n) (billAllRC x n f) (p i) (mul_pos ha (fuel_posAllRC ..)) hi (hf.width _) (bill_plusAllRC hp x n) hh

lemma accountsAllRC (H : S.Hierarchy) (A : Weight L) (h : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ D : ℕ, ∀ (x d a : ℝ) (_ : 0 ≤ d) (_ : 1≤ a) (f : Profile), Ends f → Plus f →
    (∀ᶠ n in atTop, Room (billAllRC x n f) (a*fuelAllRC d n)) → ∀ m : ℕ, D ≤ m →
    (∀ᶠ n in atTop, Integrable (fun p : E4 => Reel i (lampsAllRC m x d a f n) p * ‖p j‖^(2*k)) (ν V A)) ∧
    BudgetAllRC (max (-x) (d*D)) (fun n => ∫ p : E4, Reel i (lampsAllRC m x d a f n) p * ‖p j‖^(2*k) ∂ν V A) := by
  obtain ⟨D,hD⟩ := surface V H A h j hj k
  refine ⟨D,fun x d a hd ha f hf hp hR m hm => ?_⟩
  obtain ⟨C,hC,ht⟩ := hD m (by omega) f hf hp
  have hx n : 1 ≤ a*fuelAllRC d n := one_le_mul_of_one_le_of_one_le ha (by simpa only [fuel0AllRC] using fuel_leAllRC hd n)
  constructor
  · filter_upwards [hR] with n hh; exact (ht _ (hx n) _ (fuel_posAllRC ..) hh).1
  apply ((((budget_invAllRC x).rise (le_max_left ..)).add ((((budget_fuelAllRC d).times a).pow D).rise (le_max_right ..))).times C).signed
  · filter_upwards [hR] with n hr
    refine integral_nonneg_of_ae ?_
    filter_upwards [before V A] with p hu
    exact mul_nonneg (lamp_signsAllRC m x d a f hf hp n (by linarith) hr i p hu) (pow_nonneg (norm_nonneg _) _)
  filter_upwards [hR] with n hh
  exact (ht _ (hx n) _ (fuel_posAllRC ..) hh).2
end YM.NSF.Outer
