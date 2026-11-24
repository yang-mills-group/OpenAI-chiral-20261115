import YM.SU5.FiniteGaugeData.ArchiveK.Symphony
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] lint_prob
set_option quotPrecheck false
variable (G:E4≃ₗᵢ[ℝ] E4) (p:Space3)(a:Axis)(x:E4)
def flute (G:E4≃ₗᵢ[ℝ] E4)(p:Space3)(a:Axis) :ℂ:= ((τ/‖p‖:ℝ):ℂ)*pulseG G p a*leer (pulseG G p)^8
local notation "K"=> crestG G p
local notation "T"=> depthG G x
local notation "U" u:max=> upright G (p,u)
local notation "Σ"=> seedX G p
local notation "E"=> ‖p‖
abbrev yotta (a:Axis)(x y:E4):ℂ:= coastE (inner ℝ y x)*ironQ y a
lemma yotta_int(a:Axis) : Integrable (yotta a x):= by
 apply (ironQ_meet a).norm.mono'; · exact (Measurable.aestronglyMeasurable (show Measurable _ from Measurable.mul (contCoastE.measurable.comp (by fun_prop)) (ironQ_meas a)))
 filter_upwards with u; simp only [yotta,norm_mul,coast_pay,one_mul,le_refl]
lemma medley (p':p≠0) (e:20<T) : ∫ u, yotta a x (upright G (p,u))= flute G p a * rise (pulseG G p) x:=by
 let k:=kite G (p:=p) T; let q:=attar G p T; let c:= coastE (crestG G p x); let s:= (((seedX G p) a):ℂ); let t:= (((sailX G) a):ℂ)
 have he(u:ℝ): yotta a x (upright G (p,u))=(c*s)* k u + (c*((-Complex.I)*t))*q u:=by
    let W:= U u; have hb: ‖W‖^2=E^2+u^2:= by unfold W; rw [up_G,LinearIsometryEquiv.norm_map]; exact norm_xray ..
    have hk: inner ℝ W x=crestG G p x+T*u:= by unfold W; rw [line_G]; unfold crestG depthG; rw [inner_add_left, real_inner_smul_left, mul_comm] -- tune
    unfold yotta k q attar kite ironQ; change coastE (inner ℝ W x)*(amiX W*(2*brushQ W a/ pass (brushQ W)))=_; have ht:brushQ W a=s+(u:ℂ)*t:=by unfold W; rw [line_G]; unfold brushQ s t Fir.tmap; simp [smul_eq_mul]
    rw [hk,coast_add,spendQ, ht,hb]; unfold c whey; push_cast; ring_nf; simp only [Complex.I_sq, ← one_div, neg_mul]; ring -- tune
 simp_rw [he]; rw [integral_add ((kite_I G p' T).const_mul _) ((kite_Dt G p' T).1.const_mul _)]; simp_rw [integral_const_mul]; rw [ring_v G p' T e,releaseG G p' T e]; unfold flute c weave; have hv:0<T:=by linarith only [e]
 rw [iron_q,abs_of_pos hv]; rw [show pulseG G p a = s+(Complex.I*‖p‖)*t from rfl]; ring_nf -- tune
#check MeasurePreserving.integral_comp
abbrev sax (a:Axis)(x:E4):ℂ:= ∫ y,yotta a x y
lemma serenade (h:20<T): sax a x= ∫ p:Space3,flute G p a*rise (pulseG G p) x :=by
 unfold sax; rw [← MeasurePreserving.integral_comp (upmarket G) (upright G).measurableEmbedding (yotta a x)]; change ∫ t:Space3×ℝ,yotta a x (upright G t) ∂ ((MeasureTheory.volume (α:=Space3)).prod MeasureTheory.volume) =_; rw [integral_prod]; swap; · exact (upmarket G|>.integrable_comp_of_integrable (yotta_int x a)) -- tune order
 refine integral_congr_ae ((zero_free _).mono fun i p=> medley G i a x p h)
local notation "I"=> Complex.I
lemma pulse_pay : ‖pulseG G p a‖ ≤ 2*‖p‖:=by
 unfold pulseG; rw [Pi.add_apply]; apply (norm_add_le ..).trans; simp only [brushQ,Fir.tmap, Complex.norm_real, Pi.smul_apply, norm_smul,norm_mul,norm_I,one_mul, Real.norm_eq_abs, abs_norm]; have hu:= arm_abs (sailX G) a; rw [sail_size] at hu; have hv:= arm_abs Σ a; rw [seed_size] at hv; exact (add_le_add hv (mul_le_of_le_one_right (norm_nonneg _) hu)).trans (le_of_eq (two_mul _).symm) -- issue abs_norm simp
@[fun_prop] lemma pulse_cont : Continuous (pulseG G):=by unfold pulseG; exact (brush_safe.comp (seed_cont G)).add ((show Continuous (fun p:Space3=>Complex.I*(‖p‖:ℂ)) by fun_prop).smul continuous_const)
lemma flute_pay : ‖flute G p a‖ ≤ 2*τ*Real.exp (20*‖p‖):=by
 have hv:= tau_pos; unfold flute; by_cases p':p=0; · subst p; simp [hv,hv.le]
 have h:= norm_pos_iff.mpr p'
 rw [norm_mul,norm_mul,norm_real,Real.norm_of_nonneg (by positivity)]; refine mul_le_mul ?_ (bump G) (norm_nonneg _) (by positivity); exact (mul_le_mul_of_nonneg_left (pulse_pay ..) (show 0≤τ/‖p‖ by positivity)).trans_eq (by field_simp)
@[fun_prop] lemma flute_m : Measurable (fun p=> flute G p a):=by
 unfold flute; apply (Measurable.mul _ (((leer_safe.comp (pulse_cont G)).measurable).pow_const 8)); exact Measurable.mul (by fun_prop) ((show Continuous _ from by fun_prop).measurable)
lemma omega_int(t:20<T): Integrable (fun p:Space3=>flute G p a*rise (pulseG G p) x):=by
 apply Integrable.mono' (((exp3 (T-20) (by linarith only [t])).const_mul (2*τ))) ?_ ?_
 · apply (flute_m G a).mul (show Measurable (fun p:Space3=> _) from ?_) |>.aestronglyMeasurable; exact (rise_safe.comp ((pulse_cont G).prodMk (continuous_const (y:=x)))).measurable -- tune
 filter_upwards with v; rw [norm_mul, loftB]; refine (mul_le_mul_of_nonneg_right (flute_pay G v a) (Real.exp_pos _).le).trans_eq ?_; rw [mul_assoc,← Real.exp_add]; ring_nf
lemma sax_budget(a:Axis) : ‖sax a x‖≤ ∫ y:E4,‖ironQ y a‖ := (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ (fun i=>by dsimp only; simp [yotta])))
-- odd x.neg.R.sym. use sinc^8 even. prove mirror etc later.
@[simp] lemma sax_neg: sax a (-x)= -sax a x :=by
 let f:=yotta a (-x); unfold sax; rw [←integral_neg,← MeasureTheory.integral_neg_eq_self (f:=f)] -- tune
 refine integral_congr_ae (ae_of_all _ fun i=>?_); unfold f yotta ironQ; simp only [inner_neg_neg]; rw [show amiX (-i)=amiX i from ?_,spendQ,norm_neg,show brushQ (-i) a= -brushQ i a from (by simp [brushQ,Fir.tmap]),spendQ]; ring; unfold amiX Largo.leer; rw [Finset.prod_congr rfl (g:=fun j:Axis=> hsinc (brushQ i j/2)) (fun j _=>?_ )]; rw [rustQ,rustQ]; simp [neg_div]
#print axioms serenade
end YM.CF.Window.ArchiveK
