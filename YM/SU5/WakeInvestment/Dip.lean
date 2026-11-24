import YM.SU5.Regis.Breeze
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
-- arithmetic of signed polynomial toll. area support handled separately.
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.Regis.Wake
open Function Finset Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology Classical NNReal ENNReal BigOperators ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]
private def brush : ContDiffBump (0:ℝ):= ⟨1,2, zero_lt_one,one_lt_two⟩
private def stencil (x:ℝ) := brush x * x
def clayDip (k:ℝ)(x:ℝ):= k*stencil (x/k)
def muting (k:ℝ)(x:I→ℝ):I→ℝ:= fun i=> clayDip k (x i)
private lemma brushWorks : ∃ L:ℝ≥0,LipschitzWith L stencil:= by
 apply ContDiff.lipschitzWith_of_hasCompactSupport (n:=1) (𝕂:=ℝ) -- order proof
 · exact brush.hasCompactSupport.mul_right
 · exact brush.contDiff.mul contDiff_id
 norm_num
abbrev lipClay := brushWorks.choose
lemma lipClayWorks (k:ℝ)(v:0<k) : LipschitzWith lipClay (clayDip k):=by
 refine LipschitzWith.of_dist_le_mul (fun x y=>?_); unfold clayDip; rw [Real.dist_eq,←mul_sub,abs_mul,abs_of_pos v,←Real.dist_eq]; refine (mul_le_mul_of_nonneg_left (brushWorks.choose_spec.dist_le_mul (x/k) (y/k)) v.le).trans_eq ?_; rw [Real.dist_eq, ←sub_div, abs_div,abs_of_pos v,Real.dist_eq]; field_simp
lemma dip_smooth(k:ℝ) : ContDiff ℝ 1 (clayDip k) := contDiff_const.mul ( (show ContDiff ℝ 1 stencil from brush.contDiff.mul contDiff_id).comp (contDiff_id.div_const k))
private lemma dip_spec(k u:ℝ)(p:0<k): clayDip k u=brush (u/k)*u:=by unfold clayDip stencil; field_simp
lemma dip_same {k u:ℝ}(p:0<k)(h:|u|≤ k) : clayDip k u=u:=by rw [dip_spec k u p,show brush (u/k)=1 from brush.one_of_mem_closedBall ?_,one_mul]; rw [Metric.mem_closedBall, Real.dist_eq,sub_zero,abs_div,abs_of_pos p]; exact (div_le_one p).2 h
lemma dip_deepen{k:ℝ}(p:0<k)(x:ℝ): |clayDip k x| ≤ |x|:=by rw [dip_spec k x p,abs_mul,abs_of_nonneg brush.nonneg]; exact mul_le_of_le_one_left (abs_nonneg _) brush.le_one
lemma dip_depth{k:ℝ}(p:0<k)(x:ℝ): |clayDip k x| ≤ 2*k:=by
 by_cases h: |x|≤2*k; · exact (dip_deepen p _).trans h
 rw [dip_spec k x p, brush.zero_of_le_dist, zero_mul, abs_zero]; positivity
 rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos p]; exact (le_div_iff₀ p).mpr (le_of_not_ge h)
lemma mute_same {k:ℝ}(p:0<k)(x:I→ℝ)(h: ‖x‖≤ k):muting k x=x:= funext (fun i=> dip_same p ((norm_le_pi_norm x i).trans h))
lemma mute_shrink {k:ℝ}(p:0<k)(x:I→ℝ):‖muting k x‖≤ ‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=> (dip_deepen p (x i)).trans (norm_le_pi_norm x i))
lemma mute_ceiling{k:ℝ}(p:0<k)(x:I→ℝ):‖muting k x‖≤ 2*k:= (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) p.le)).2 (fun i=> dip_depth p (x i))
lemma mute_mix (k:ℝ)(h:0<k) (x y:I→ℝ) : ‖muting k x - muting k y‖ ≤ lipClay * ‖x-y‖:= by
 let L:ℝ:= lipClay; have ht:0≤ L:= NNReal.coe_nonneg lipClay; apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht (norm_nonneg _))).mpr; intro i; exact ((lipClayWorks k h).norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (x-y) i) ht)
lemma mute_smooth (k:ℝ) : ContDiff ℝ 1 (muting (I:=I) k):= contDiff_pi.mpr (fun i=> (dip_smooth k).comp (contDiff_apply ℝ ℝ i))
variable (U:I → StrongDual ℝ E)
abbrev drip(x:E)(i:I) := U i x
local notation "μ" => stdGaussian E
private def postage (x:E)(m:ℕ) : ℝ:= Real.exp 1 * Nat.factorial m * (1+∑ i:I,(Real.exp (U i x)+Real.exp (-(U i x))))
private lemma breath (x:E)(m:ℕ): (‖drip U x‖+1)^m ≤ postage U x m:=by
 let a:= ‖drip U x‖; let f:= ∑ i:I,(Real.exp (U i x)+Real.exp (-(U i x))); let c:ℝ:=Nat.factorial m
 have hF: Real.exp a ≤ 1+ f:=by
    cases isEmpty_or_nonempty I
    · rw [show a=0 from (by unfold a; rw [show drip U x=0 from funext fun i=> isEmptyElim i,norm_zero]),Real.exp_zero]; have h:0≤f:=sum_nonneg (fun i _=> add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le); linarith only [h]
    obtain ⟨i,L⟩:= (IsGreatest.pi_norm (drip U x)).1
    have h: |U i x|=a:=L; rw [←h]; refine le_trans ?_ ( (single_le_sum (f:=fun i:I=> (Real.exp (U i x)+ Real.exp (-(U i x)))) (fun i _=> add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) -- term infer
    rcases le_total (U i x) 0 with p|p; · rw [abs_of_nonpos p]; apply le_add_of_nonneg_left; positivity
    rw [abs_of_nonneg p]; apply le_add_of_nonneg_right; positivity
 have hc:0<c:=Nat.cast_pos.mpr (Nat.factorial_pos _)
 have hg:(a+1)^m≤ Real.exp (a+1)* c:= (div_le_iff₀ hc).1 (Real.pow_div_factorial_le_exp _ (add_nonneg (norm_nonneg _) zero_le_one) m)
 rw [Real.exp_add] at hg; unfold postage; change _≤ Real.exp 1*c*(1+ f); nlinarith only [hg,mul_le_mul_of_nonneg_left hF (show 0≤Real.exp 1*c from mul_nonneg (Real.exp_pos _).le hc.le)]
lemma wind_int (L:StrongDual ℝ E)(t:ℝ) : Integrable (fun i=> Real.exp (t*L i)) μ:= by
 apply (mgf_pos_iff (X:=⇑L) (t:=t)).1; rw [exp_linear]; exact Real.exp_pos _
private lemma meter(c:ℝ)(L:StrongDual ℝ E)(p:‖L‖≤ c):
      Integrable (fun i=> Real.exp (L i)+Real.exp (-(L i))) μ ∧ (∫ i, (Real.exp (L i)+Real.exp (-(L i))) ∂μ) ≤ 2*Real.exp (c^2/2):=by
 let F(t:ℝ)(i:E):=Real.exp (t*L i); let W:= Real.exp (c^2/2)
 have h(t:ℝ): Integrable (F t) μ:= wind_int L _
 have he (t:ℝ)(p':t^2=1): ∫ i,F t i∂μ ≤ W:=by change mgf (⇑L) _ _ ≤ _; rw [exp_linear,p',mul_one]; apply Real.exp_monotone; gcongr
 have hp: Integrable (fun i=>F 1 i+F (-1) i) μ ∧ (∫ i, (F 1 i+F (-1) i)∂μ) ≤ W+W:=⟨(h _).add (h _), (integral_add (h _) (h _)).le.trans (add_le_add (he _ (by norm_num)) (he _ (by norm_num)))⟩
 simpa only [F,W,one_mul,neg_mul,two_mul] using hp
abbrev assay (m:ℕ)(B n:ℝ):ℝ:= Real.exp 1 * Nat.factorial m * (1+n * (2*Real.exp (B^2/2)))
lemma assay_non (m:ℕ)(B v:ℝ)(p:0 ≤ v) : 0 ≤ assay m B v:=by unfold assay; positivity
lemma cloud_trial(m:ℕ)(B:ℝ)(p:∀ i, ‖U i‖ ≤ B): Integrable (fun x=>(‖drip U x‖+1)^m) μ ∧ (∫ x,(‖drip U x‖+1)^m∂μ) ≤ assay m B (Fintype.card I):=by
 let f(x:E):=(‖drip U x‖+1)^m; let A(i:I)(x:E):= Real.exp (U i x)+Real.exp (-(U i x)); let H(x:E):= postage U x m; let M:= (2*Real.exp (B^2/2)); let N:=Real.exp 1*(Nat.factorial m:ℝ); have hh:0≤N:=mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)
 have ht(i):Integrable (A i) μ:= (meter B (U i) (p i)).1
 have hB(x:E): H x=N*(1+∑ i:I, A i x):=rfl
 have h:Integrable H μ:=(((integrable_const (1:ℝ)).add (integrable_finsetSum _ (fun i _=> ht i))).const_mul _)
 have hf:Integrable f μ:= h.mono' (by let t:Continuous (drip U):= continuous_pi fun i=> (U i).continuous; exact (((t.norm).add continuous_const).pow _).aestronglyMeasurable ) (Eventually.of_forall fun x=> (Real.norm_of_nonneg (show 0≤f x from pow_nonneg (add_nonneg (norm_nonneg _) zero_le_one) _)).le.trans (breath U x m))
 refine ⟨hf,le_trans (integral_mono hf h (fun i=>breath U i m)) ?_⟩
 change (∫ x:E, N*(1+∑ i:I,A i x)∂μ)≤_; rw [integral_const_mul,integral_add (integrable_const _) (integrable_finsetSum _ (fun i _=> ht i)),integral_finsetSum _ (fun i _=> ht i),integral_const,probReal_univ,one_smul]; apply mul_le_mul_of_nonneg_left (add_le_add_right _ _) hh
 exact (sum_le_sum (fun i _=> (meter B (U i) (p i)).2)).trans_eq (by simp)
-- semantic polynomial credentials. arity can be 0. Also budgets heightened in layout parent. Assures margin in comparison site boxes even while paying a cap tail.
structure Paint (G:(I→ℝ)→ℂ)(m:ℕ)(C:ℝ) : Prop where
 bright : ContDiff ℝ 1 G
 worth(K:ℝ)(p:1≤K)(x:I→ℝ) (t:‖x‖≤ K) : ‖G x‖≤ C*K^m
 price(K:ℝ)(p:1≤K)(x y:I→ℝ)(sx:‖x‖≤K)(sy:‖y‖≤K): ‖G x-G y‖ ≤ C*K^m* ‖x-y‖
variable {G:(I→ℝ)→ℂ}{m:ℕ}{K C k:ℝ} (p:Paint G m C)
include p
namespace Paint
lemma nonneg: 0≤C:=by
 have h:= (norm_nonneg (G 0)).trans (p.worth 1 le_rfl 0 (by rw [norm_zero]; exact zero_le_one)); simpa using h
lemma fade_cost(h:1 ≤ k)(x:I→ℝ): ‖G (muting k x)‖ ≤ C*(2*k)^m:= p.worth _ (by linarith) _ (mute_ceiling (zero_lt_one.trans_le h) x)
lemma fade_lip (h:1 ≤ k)(x y:I→ℝ): ‖G (muting k x) - G (muting k y)‖ ≤ C*(2*k)^m * (lipClay:ℝ)*‖x-y‖:=by
 have h0:= zero_lt_one.trans_le h; exact (p.price _ (by linarith) _ _ (mute_ceiling h0 x) (mute_ceiling h0 y)).trans ((mul_le_mul_of_nonneg_left (mute_mix k h0 x y) (mul_nonneg p.nonneg (by positivity))).trans_eq (mul_assoc ..).symm)
lemma shade_n (h:1 ≤ k)(n:ℕ)(x:I→ℝ): ‖G x-G (muting k x)‖ ≤ 2*C / k^n*(‖x‖+1)^(m+n):=by
 let a:= ‖x‖+1; have hK:= zero_lt_one.trans_le h; have ha:1 ≤ a:= le_add_of_nonneg_left (norm_nonneg _); let t:=C*a^m; have hc:=p.nonneg; by_cases v: ‖x‖≤k
 · rw [mute_same hK x v,sub_self,norm_zero]; positivity
 have hv:k≤a:=le_trans (le_of_not_ge v) (le_add_of_nonneg_right zero_le_one); have hg:0≤ t:=mul_nonneg hc (pow_nonneg (zero_le_one.trans ha) _)
 change _ ≤ 2*C/k^n*a^(m+n); apply (norm_sub_le ..).trans; rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hK _)];
 have hu: ‖x‖≤ a:=le_add_of_nonneg_right zero_le_one
 refine (mul_le_mul (add_le_add (p.worth a ha _ hu) (p.worth a ha _ ((mute_shrink hK x).trans hu))) (pow_le_pow_left₀ hK.le hv n) (pow_nonneg hK.le _) (add_nonneg hg hg)).trans_eq ?_; rw [pow_add]; ring
lemma soak (B:ℝ)(v:∀ i, ‖U i‖ ≤ B): Integrable (fun x=>G (drip U x)) μ ∧ ‖∫ x, G (drip U x) ∂μ‖ ≤ C*assay m B (Fintype.card I):=by
 let T x:= G (drip U x); let V x:= (‖drip U x‖+1)^m; have hc:=p.nonneg; obtain ⟨hv,qp⟩:=cloud_trial U m B v
 have hh(x:E): ‖T x‖ ≤ C*V x:=p.worth _ (le_add_of_nonneg_left (norm_nonneg _)) _ (le_add_of_nonneg_right zero_le_one)
 have ht:Integrable T μ:= (hv.const_mul C).mono' ( (p.bright.continuous.comp (continuous_pi fun j=> (U j).continuous)).aestronglyMeasurable) (Eventually.of_forall hh)
 refine ⟨ht, le_trans (norm_integral_le_integral_norm T) ((integral_mono ht.norm (hv.const_mul C) hh).trans ?_)⟩; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left qp hc
lemma faded_int (h:1≤k): Integrable (fun x=>G (muting k (drip U x))) μ:= (integrable_const («μ»:=μ) (C*(2*k)^m)).mono' ( (p.bright.continuous.comp ((mute_smooth (I:=I) k).continuous.comp (continuous_pi fun j=> (U j).continuous))).aestronglyMeasurable) (Eventually.of_forall fun x:E=> fade_cost p h (drip U x))
lemma receipts (h:1≤k)(n:ℕ)(B:ℝ)(v:∀ i, ‖U i‖ ≤ B): ‖(∫ x, G (drip U x) ∂μ) - (∫ x,G (muting k (drip U x)) ∂μ)‖ ≤ 2*C/k^n*assay (m+n) B (Fintype.card I):=by
 obtain ⟨hb,hv⟩:= soak U p B v; let T x:= G (drip U x)- G (muting k (drip U x)); rw [← integral_sub hb (faded_int U p h)]; obtain ⟨a,b⟩:= cloud_trial U (m+n) B v
 refine le_trans (norm_integral_le_integral_norm T) ((integral_mono ((hb.sub' (faded_int U p h)).norm) (a.const_mul _) (fun x=> p.shade_n h n (drip U x))).trans ?_)
 rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left b (by have ht:= p.nonneg; have hv:=zero_lt_one.trans_le h; positivity)
end Paint
end YM.Regis.Wake
#print axioms YM.Regis.Wake.Paint.receipts
