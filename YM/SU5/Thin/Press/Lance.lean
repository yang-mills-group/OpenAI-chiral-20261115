import YM.SectorNext.VACUUM_NORMALIZATION.Laplace
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Sleigh
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory SectorNext.Vacuum
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations Metric
lemma exp_swing{a b w:ℝ} (ha:a≤w)(hb:b≤w): |Real.exp a-Real.exp b|≤ Real.exp w*|a-b|:= (convex_Iic (𝕜:=ℝ) w).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (fun x h => by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone h) hb ha
lemma log_swing{a b w:ℝ} (p:0<w)(ha:w≤a)(hb:w≤b): |Real.log a-Real.log b|≤ w⁻¹*|a-b|:= (convex_Ici (𝕜:=ℝ) w).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x h => (Real.hasDerivAt_log (show x≠0 from (p.trans_le h).ne')).hasDerivWithinAt) (fun x h => by rw [Real.norm_of_nonneg (inv_pos.mpr (p.trans_le h)).le]; exact inv_anti₀ p h) hb ha
lemma time_drip (n:ℕ){t:ℝ}(p:0<t): Tendsto (fun x:ℝ=>x^n*Real.exp (-(t*x))) atTop (𝓝 0):=by simpa only [Real.rpow_natCast,neg_mul] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) t p)
lemma snow_max (n:ℕ){a:ℝ}(p:0<a): ∃ t>(0:ℝ),∀ r≥(0:ℝ), r^n*Real.exp (-a*r^2)≤t:=by
 obtain ⟨x,u⟩:= eventually_atTop.mp ((time_drip n p).eventually (ge_mem_nhds zero_lt_one))
 let R:=max x 1; let z:=(x:ℝ)
 have hR:1≤R:=le_max_right ..
 refine ⟨R^n,by have h:=zero_lt_one.trans_le hR; positivity,fun t h=>?_⟩
 rcases le_total t R with v|v; exact (mul_le_of_le_one_right (pow_nonneg h _) (Real.exp_le_one_iff.mpr (by have hz:=sq_nonneg t; nlinarith))).trans (pow_le_pow_left₀ h v _)
 refine (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (pow_nonneg h n)).trans ((u t ((le_max_left ..).trans v)).trans (one_le_pow₀ hR))
 have hx:1≤t:=hR.trans v; linarith only [mul_le_mul_of_nonneg_left (show t≤t^2 by nlinarith) p.le]
section
variable (E:Type*)[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]{a:ℝ}
lemma gauss_owned (ha:0<a):Integrable (fun x:E=>Real.exp (-a*‖x‖^2)):=by
  have hg:=(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(a:ℂ)) (by exact ha) 0 (0:E)).norm
  simpa [Complex.norm_exp,pow_two,Complex.mul_re] using hg
lemma gauss_touch (n:ℕ)(p:0<a) : Integrable (fun x:E=>‖x‖^n*Real.exp (-a*‖x‖^2)):=by
 obtain ⟨D,d,H⟩:=snow_max n (half_pos p)
 refine ((gauss_owned E (half_pos p)).const_mul D).mono (by fun_prop) (Eventually.of_forall fun x=> ?_)
 rw [Real.norm_of_nonneg (by positivity:(0:ℝ)≤ ‖x‖^n*_), Real.norm_of_nonneg (by positivity:(0:ℝ)≤ D* Real.exp (-(a/2)*‖x‖^2))]
 let u:=Real.exp (-(a/2)*‖x‖^2)
 calc
 _= (‖x‖^n*u)*u:=by unfold u; rw [mul_assoc,←Real.exp_add]; ring_nf
 _≤ _:=mul_le_mul_of_nonneg_right (H _ (norm_nonneg _)) (Real.exp_pos _).le
end
variable {G:Gauge}{A:ChartRatio G}(H:LocalRatio A){r D κ:ℝ}
def fiord (A:ChartRatio G)(κ r t:ℝ)(x:G.Color):= (closedBall (0:G.Color) r).indicator (fun y => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) (t⁻¹ • x)
def estuary (A:ChartRatio G)(κ:ℝ)(x:G.Color):= A.scale*Real.exp (-(κ/2)*‖x‖^2)
include H in
lemma jacob (v:0<r)(w:r<A.radius): ∃ C>(0:ℝ),∀ x:G.Color, ‖x‖ ≤ r → |A.J x-1|≤ C*‖x‖:=by
 let I:= closedBall (0:G.Color) r
 have ht x (p:x∈I):= H.germ x (closedBall_subset_ball w p)
 have hx:ContinuousOn (fun x:G.Color=> ‖fderiv ℝ A.J x‖) I:= (fun x h=> ((ht x h).fderiv_right (m:=0) (by norm_num)).continuousAt.norm.continuousWithinAt)
 obtain ⟨C,c⟩:= IsCompact.bddAbove_image (ProperSpace.isCompact_closedBall (0:G.Color) r) hx
 let a:=max 1 C; have ha:1≤a:= le_max_left ..
 refine ⟨a,zero_lt_one.trans_le ha,fun x p=>?_⟩
 have he:= (convex_closedBall (0:G.Color) r).norm_image_sub_le_of_norm_fderiv_le (f:=A.J) (fun i h=> (ht i h).differentiableAt (by norm_num)) (C:=a) (fun x w=> le_trans (c (mem_image_of_mem _ w)) (le_max_right ..)) (mem_closedBall_self v.le) (mem_closedBall_zero_iff.mpr p)
 rwa [sub_zero,H.anchored,Real.norm_eq_abs] at he
lemma numeric_rim {t z p q r d κ:ℝ} (h:0<t)(hp:0≤p)(g:t*p=z)(u:p≤r)(he:0≤d)(k:0<κ)(f:p/2≤q)(hx:|q-p|≤d*p^2): |Real.exp (-(κ/2)*(t*q)^2) - Real.exp (-(κ/2)*z^2)| ≤ t⁻¹ * ((Real.exp (-(κ/8)*z^2)) * (κ/2*(2+d*r)*d*z^3)):=by
 have hv:0≤z:=g ▸ mul_nonneg h.le hp
 have hs:t*p≤2*(t*q):=by have he:= mul_le_mul_of_nonneg_left f h.le; linarith
 have h':0≤ q:=by linarith
 have hd:t*q≤ (1+d*r)*z:=by
    have hy:q≤ (1+d*r)*p:=by nlinarith only [(abs_le.mp hx).2,mul_le_mul_of_nonneg_left u (mul_nonneg he hp)]
    rw [←g]; exact (mul_le_mul_of_nonneg_left hy h.le).trans_eq (by ring)
 have hQ:|t*q-z|≤ t⁻¹*d*z^2:=by rw [←g,←mul_sub,abs_mul,abs_of_pos h]; exact (mul_le_mul_of_nonneg_left hx h.le).trans_eq (by field_simp)
 let y:= Real.exp (-(κ/8)*z^2)
 have h₁:-(κ/2)*(t*q)^2 ≤ -(κ/8)*z^2:=by
    have hc:z^2 ≤ (2*(t*q))^2:= pow_le_pow_left₀ hv (g ▸ hs) _
    nlinarith only [mul_le_mul_of_nonneg_left hc k.le]
 have h₂:-(κ/2)*z^2 ≤ -(κ/8)*z^2:=by nlinarith [mul_nonneg k.le (sq_nonneg z)]
 apply (exp_swing h₁ h₂).trans; rw [show (-(κ/2)*(t*q)^2)-(-(κ/2)*z^2) = -(κ/2)*((t*q-z)*(t*q+z)) by ring,abs_mul,abs_mul,abs_neg,abs_of_pos (half_pos k),abs_of_nonneg (by positivity : 0 ≤ t*q+z)]
 have h:=mul_le_mul hQ (show t*q+z≤ (2+d*r)*z by linarith only [hd]) (by positivity) (by positivity)
 exact ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (half_pos k).le) (Real.exp_pos _).le)).trans_eq (by ring)
end YM.Sleigh
