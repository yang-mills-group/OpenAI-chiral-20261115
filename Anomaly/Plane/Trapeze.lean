import Anomaly.Plane.Verse
import Anomaly.Market.Jewel
/-! O(K^-1), taking K≥1. -/
set_option autoImplicit false
set_option maxHeartbeats 333333
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric MeasureTheory NormedSpace ProbabilityTheory Finset
open GeometryP
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] {ι:Type*} [Fintype ι] (x y z w:E) {k:ℝ}
private lemma snub_four (a:1 ≤ k)(F:Fin 4→ℝ): |(∏ i:Fin 4,snub k (F i))-∏ i,F i| ≤ 2*(∑ i,F i ^8)/k:=by
 let X:= ∏ i:Fin 4,snub k (F i)
 let Y:= ∏ i,F i
 have p:0<k:=by linarith
 have ht(i): |snub k (F i)|≤|F i|:=(snub_budget p _).2.1
 obtain ⟨j,g,h⟩:=Finset.exists_max_image (univ:Finset (Fin 4)) (fun i=>|F i|) univ_nonempty
 let u:=|F j|
 have hg(i): |F i|≤ u:= h i (mem_univ _)
 by_cases r:u≤k
 · change |(∏ i,snub k (F i))-Y|≤_; rw [prod_congr (s₂:=univ) rfl (fun i _=>(snub_budget p _).2.2 ((hg i).trans r)),show ∏ i,F i=Y from rfl,sub_self,abs_zero]; positivity
 have hh:k≤ u:=le_of_not_ge r
 have hX: |∏ i,snub k (F i)| ≤ u^4:=by rw [abs_prod]; exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=> (ht i).trans (hg i))).trans_eq (by simp)
 have hY: |Y|≤u^4:=by unfold Y; rw [abs_prod]; exact (prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=> hg i)).trans_eq (by simp)
 refine (le_trans (abs_sub _ _) ?_); refine (add_le_add hX hY).trans (?_); rw [le_div_iff₀ p]; have hz:k ≤ u^4:= hh.trans (le_self_pow₀ (a.trans hh) (by decide)); have hx':u^8 ≤ ∑ i,F i^8 := by rw [show u^8=F j^8 from Even.pow_abs (by decide: Even 8) _]; exact single_le_sum (f:=fun i => F i^8) (fun i _=>by positivity) (mem_univ j)
 nlinarith only [hx',mul_le_mul_of_nonneg_left hz (sq_nonneg (u^2))]
abbrev pat (x y:E)(k:ℝ)(v:E) := snub k (A x v)*snub k (A y v)
lemma pat_bold {x y:E} (u:0<k): MemLp (pat x y k) 2 (stdGaussian E):=by
 refine MemLp.of_bound ?_ ((2*k)^2) (.of_forall fun i=>?_)
 · have ht: Continuous (snub k):= (cutCont _).continuous; apply Continuous.aestronglyMeasurable; unfold pat A; exact (ht.comp (continuous_const.inner continuous_id)).mul (ht.comp (continuous_const.inner continuous_id))
 rw [Real.norm_eq_abs,pat,abs_mul,pow_two]; exact mul_le_mul (snub_budget u _).1 (snub_budget u _).1 (abs_nonneg _) (by positivity)
abbrev fare4 (D k:ℝ):= 8*105*D^8/k
lemma peace4 (a:1 ≤ k) (F:Fin 4→E)(B:ℝ)(h:∀ i,‖F i‖ ≤ B): let C:= pat (F 0) (F 1) k * pat (F 2) (F 3) k; |(∫ x,C x∂stdGaussian E)-pairing (F 0) (F 1) (F 2) (F 3)| ≤ fare4 B k:=by
 intro V; let A:= fun v:E=> mats (F 0) (F 1) v*mats (F 2) (F 3) v
 have ht:0 < k:=by linarith
 have hv:Integrable V (stdGaussian E):= (pat_bold ht).integrable_mul (pat_bold ht)
 have he:Integrable A (stdGaussian E):=(mats_bold ..).integrable_mul (mats_bold ..)
 let g:= fun v:E=> 2*talents F 4 v/k; have hg:= (partT F 4).integrable (show (1:ℝ≥0∞) ≤ 2 by norm_num); have hf: Integrable g (stdGaussian E):= (hg.const_mul 2).div_const k
 have hh(v): |V v-A v| ≤ g v:=by
    have hx:= snub_four a (fun i=> inner ℝ (F i) v); simp only [Fin.prod_univ_succ,Fin.prod_univ_zero, mul_one,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hx  -- defeq tune names
    simpa only [show (2:Fin 3).succ=(3:Fin 4) by rfl,show (4*2:Nat)=8 by rfl,V,g,A,talents,Pier.A,Pi.mul_apply,pat,mats,mul_assoc] using hx
 change |(∫ x,V x∂stdGaussian E)-∫ x,A x∂stdGaussian E|≤_; rw [←integral_sub hv he]; refine le_trans (norm_integral_le_of_norm_le (f:=fun a:E=>V a-A a) hf (.of_forall hh)) ?_
 unfold g; rw [integral_div,integral_const_mul]; have ht:=tin_four F ((norm_nonneg _).trans (h 0)) h; apply le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)) (by linarith only [a])); exact le_of_eq (by simp [balboa,fare4]; ring)
end YM.Regis.Head.Brecht.Pier
