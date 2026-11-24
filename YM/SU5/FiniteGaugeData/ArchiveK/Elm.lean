import YM.SU5.FiniteGaugeData.ArchiveK.Wisp
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
variable (x:E4)
open Set
abbrev amiX:= leer (brushQ x)^8
lemma born_four : Module.finrank ℝ E4=4:= by simp [E4,Axis]
lemma born_three : Module.finrank ℝ Space3=3:= by simp [Space3,SpaceAxis]
lemma rustQ(i:Axis): hsinc (brushQ x i/2)=Real.sinc (x i/2):= by rw [show brushQ x i/2=((x i/2:ℝ):ℂ) from (by unfold brushQ Fir.tmap; push_cast; rfl),h_real]
@[fun_prop] lemma leer_safe : Continuous leer:=by unfold leer; have he:= hschi.continuous; fun_prop
@[fun_prop] lemma ami_safe : Continuous amiX:= by unfold amiX; fun_prop
lemma ami_le : ‖amiX x‖ ≤ 1:=by
 unfold amiX Largo.leer; rw [norm_pow, norm_prod]; apply pow_le_one₀ (by positivity); apply Finset.prod_le_one; intro;intro; positivity; intro a _; rw [rustQ]; simpa using Real.abs_sinc_le_one _
lemma aba (p:x≠0): ‖amiX x‖ ≤ (4/‖x‖)^8:=by
 obtain ⟨i,t⟩:= one_arm x; have hv:0<‖x‖:= norm_pos_iff.mpr p; have hx:0< |x i|:= (by linarith only [hv,t]); let f(i:Axis):=hsinc (brushQ x i/2); change ‖(∏ i,f i)^8‖≤_; rw [norm_pow,norm_prod]; apply pow_le_pow_left₀ (by positivity); rw [← mul_prod_erase (f:=fun i=>‖f i‖) _ (Finset.mem_univ i)]; refine (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=> norm_nonneg _) (fun i _=>?_))).trans ?_
 · unfold f; rw [rustQ]; simpa using Real.abs_sinc_le_one _
 unfold f; rw [rustQ,Complex.norm_real,Real.norm_eq_abs,Real.sinc_of_ne_zero (div_ne_zero (abs_pos.mp hx) (by norm_num)), abs_div,abs_div,abs_of_nonneg (by norm_num: (0:ℝ)≤2)]; rw [div_le_div_iff₀ (half_pos hx) hv]; exact (mul_le_of_le_one_left hv.le (Real.abs_sin_le_one _)).trans (t.trans (le_of_eq (by ring)))
abbrev ironQ(a:Axis): ℂ:= amiX x*(2*(brushQ x a)/pass (brushQ x))
lemma ashQ(a:Axis)(h:x≠0): ‖ironQ x a‖ ≤ ‖amiX x‖*(2/‖x‖):=by
 rw [ironQ,norm_mul,norm_div, spendQ]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); have hm:0<‖x‖:=norm_pos_iff.mpr h; have hp:=arm_abs x a
 rw [norm_mul]; norm_num; have he:‖brushQ x a‖=|x a|:=by simp [brushQ,tmap];
 rw [he]; rw [div_le_div_iff₀ (by positivity) hm]; nlinarith only [mul_le_mul_of_nonneg_right hp hm.le]
@[fun_prop] lemma ironQ_meas (a:Axis): Measurable (fun x:E4=> ironQ x a):=by unfold ironQ; simp_rw [spendQ]; have hf:=ami_safe.measurable; have hv:=brush_safe.measurable; fun_prop
lemma ironQ_meet(a:Axis): Integrable (fun x:E4=> ironQ x a):= by
 let f(x:E4):=ironQ x a; let S:=Metric.ball (0:E4) 1; have he: IntegrableOn f S:=by
    apply integrableOn_ball_of_norm_le_rpow (C:=2) (by rw [born_four]; decide) (α:=1) (by rw [born_four]; norm_num) _ ((ironQ_meas _).aestronglyMeasurable); apply ae_restrict_of_ae ((zero_free (μ:=(MeasureTheory.volume : Measure E4))).mono ?_); intro x t; refine (ashQ x a t).trans ((mul_le_of_le_one_left (by positivity : 0≤ 2/‖x‖) (ami_le x)).trans_eq ?_); rw [Real.rpow_neg_one]; ring
 rw [← integrableOn_univ, ← Set.union_compl_self S]; apply he.union; let D(x:E4):= (1+‖x‖)^(-(8:ℝ)); have hh:= (show Integrable D from integrable_one_add_norm (by rw [born_four]; norm_num)); apply Integrable.mono' (g:=fun x=> (8^8*2:ℝ)*D x) ((hh.const_mul _).integrableOn) (ironQ_meas _).aestronglyMeasurable ?_
 filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet.compl : MeasurableSet Sᶜ)] with x hx; simp only [Set.mem_compl_iff,mem_ball_zero_iff,S,not_lt] at hx; have hz:0<‖x‖:= zero_lt_one.trans_le hx; refine (ashQ x a (norm_pos_iff.mp hz)).trans ?_; have hv:= aba x (norm_pos_iff.mp hz); refine (mul_le_mul hv (div_le_self zero_le_two hx) (show 0≤ 2/‖x‖ by positivity) (by positivity)).trans ?_
 have hp: 4/‖x‖ ≤8/(1+‖x‖):=by rw [div_le_div_iff₀ hz (by positivity)]; linarith only [hx]
 unfold D; simp only [Real.rpow_neg (by positivity:0≤1+‖x‖), Real.rpow_ofNat]; apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ 4/‖x‖) hp 8) zero_le_two) (le_of_eq ?_); rw [div_pow]; ring
-- conic representation real.Fix z; multiply ratio× sinc.Pow. uses derivative time*B.
abbrev rockF (G:E4≃ₗᵢ[ℝ] E4) (p:Space3)(u:ℝ)(j:ℕ):ℝ:= ‖amiX (upright G (p,u))‖*(|u|^j / (‖p‖^2+u^2))
lemma side_full (G:E4≃ₗᵢ[ℝ] E4) (p:Space3) (t:p≠0)(j:ℕ)(z:j≤1) : Integrable (rockF G p · j):=by
 let F(u:ℝ):= rockF G p u j
 have hf:Continuous (fun u:ℝ=>upright G (p,u)):= by simp_rw [up_G]; change Continuous (fun u:ℝ=> G (rectX (WithLp.toLp 2 (p,u)))); fun_prop
 have hp(u:ℝ):0<‖p‖^2+u^2:= add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr t) _) (sq_nonneg _); have he:Continuous F:= by unfold F rockF; (apply Continuous.mul ((ami_safe.comp hf).norm); exact (Continuous.div (by fun_prop) (by fun_prop) (fun i=> (hp _).ne')));
 let S:=Metric.closedBall (0:ℝ) 1; rw [←integrableOn_univ,←Set.union_compl_self S]; apply (he.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).union; have hh: Integrable (fun u:ℝ=>(1+‖u‖)^(-(8:ℝ))):= integrable_one_add_norm (by norm_num); let Y:= (8:ℝ)^8; apply Integrable.mono' ((hh.const_mul Y).integrableOn) he.aestronglyMeasurable ?_
 filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet.compl : MeasurableSet Sᶜ)] with u hx; simp only [Set.mem_compl_iff,mem_closedBall_zero_iff,Real.norm_eq_abs,not_le,S] at hx -- tune
 let q:= upright G (p,u); have ht:1 ≤ |u|:=by simpa [hx] using hx.le ; -- tune
 have hu:0 < |u|:=zero_lt_one.trans_le ht; have hv:0<‖p‖:= norm_pos_iff.mpr t; have hb : ‖q‖^2=‖p‖^2+u^2:= (by unfold q; rw [up_G,LinearIsometryEquiv.norm_map]; exact norm_xray ..); have hM: |u| ≤ ‖q‖:= (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by rw [sq_abs,hb]; exact le_add_of_nonneg_left (sq_nonneg _)); have hg:0<‖q‖:=hu.trans_le hM
 unfold F rockF; rw [Real.norm_of_nonneg (by positivity)]; refine (mul_le_of_le_one_right (norm_nonneg _) ((div_le_one (hp u)).2 ?_)).trans ?_
 · refine (pow_le_pow_right₀ ht z).trans ?_; rw [pow_one]; nlinarith only [ht, hu,sq_abs u,sq_nonneg ‖p‖]
 refine (aba q (norm_pos_iff.mp hg)).trans ?_; unfold Y; have hk : 4/‖q‖ ≤8/(1+|u|):=by rw [div_le_div_iff₀ hg (by positivity)]; linarith only [hM,ht]
 rw [Real.rpow_neg (by positivity:0≤ 1+‖u‖),Real.rpow_ofNat]; refine (pow_le_pow_left₀ (by positivity) hk 8).trans_eq (by rw [div_pow, Real.norm_eq_abs]; ring) -- norm_eq_abs
lemma exp3(c:ℝ)(t:0<c): Integrable (fun p:Space3=> Real.exp (-c*‖p‖)):= by
 let F(x:ℝ):=Real.exp (-c*x); let H:=MeasureTheory.integrable_fun_norm_addHaar (MeasureTheory.volume : Measure Space3) (f:=F); unfold F at H; rw [born_three] at H; refine H.2 ?_ -- Nat subtraction.
 let h:= integrableOn_rpow_mul_exp_neg_mul_rpow (b:=c) (s:=2) (p:=1) (by norm_num) (by norm_num) t; refine h.congr ?_ -- tune syntax
 filter_upwards with x; simp
lemma exp3_poly(c:ℝ)(t:0<c)(n:ℕ): Integrable (fun p:Space3=> ‖p‖^n * Real.exp (-c*‖p‖)):= by
 let F(x:ℝ):= x^n* Real.exp (-c*x); let H:=MeasureTheory.integrable_fun_norm_addHaar (MeasureTheory.volume : Measure Space3) (f:=F); unfold F at H; rw [born_three] at H; let h:= integrableOn_rpow_mul_exp_neg_mul_rpow (b:=c) (s:=((n+2:ℕ):ℝ)) (p:=1) (by exact lt_trans (show (-1:ℝ)<0 by norm_num) (by exact_mod_cast (show 0<n+2 by omega))) (by norm_num) t; refine H.2 (h.congr ?_)
 filter_upwards with x; rw [Real.rpow_natCast,Real.rpow_one]; simp [pow_add, mul_left_comm, mul_assoc]
#print axioms ironQ_meet
end YM.CF.Window.ArchiveK
