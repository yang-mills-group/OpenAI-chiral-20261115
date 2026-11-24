/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SectorNext.VACUUM_NORMALIZATION.Laplace

-- Sharpening P1. This buys quantitative single-bond purchase, on the same LocalRatio as retail.
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory Metric
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations
variable {G : Gauge}
private def perle (A : ChartRatio G) (κ r t : ℝ) (x : G.Color) :=
 (closedBall 0 r).indicator (fun y => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) (t⁻¹ • x)

lemma expo_lipschitz_top {x y c:ℝ}(hx:x≤c)(hy:y≤c): |Real.exp x - Real.exp y| ≤ Real.exp c*|x-y|:=by
 rw [← Real.norm_eq_abs,← Real.norm_eq_abs]
 exact Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.exp) (fun _ _ => Real.differentiable_exp.differentiableAt)
   (fun i hi=>by rw [Real.deriv_exp,Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_exp.mpr hi) (convex_Iic c) hy hx -- order

lemma boltz {k:ℝ} (hk: 0 < k) (n : ℕ):
  ∃ C>0,∀ r ≥ 0,r^n*Real.exp (-k*r^2) ≤ C*Real.exp (-(k/2)*r^2):=by
 let b := k/2
 let g(x:ℝ) := x^n*Real.exp (-b*x^2)
 have h:Tendsto g atTop (𝓝 0):=by
   have h₀:=(rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (show 0<b from half_pos hk) (n:ℝ));
   simpa [g] using h₀.tendsto_zero_of_tendsto (Real.tendsto_exp_atBot.comp (Filter.Tendsto.const_mul_atTop_of_neg (by norm_num : -(1/2:ℝ) < 0) tendsto_id))
 obtain ⟨u,hu⟩:=eventually_atTop.mp (h.eventually (ge_mem_nhds zero_lt_one))
 obtain ⟨t,ht⟩:=((show IsCompact (Icc (0:ℝ) u) from isCompact_Icc).image (show Continuous g by unfold g; fun_prop)).bddAbove
 refine ⟨max 1 t,zero_lt_one.trans_le (le_max_left ..),fun x hx=>?_⟩
 have hi: g x ≤ max 1 t:= (le_total x u).elim (fun h'=>le_trans (ht (mem_image_of_mem g (show x∈Icc (0:ℝ) u from ⟨hx,h'⟩))) (le_max_right ..)) (fun h'=>le_trans (hu x h') (le_max_left ..))
 rw [show -k*x^2 = -(k/2)*x^2 + (-b*x^2) from by unfold b; ring,Real.exp_add,mul_comm (Real.exp _),← mul_assoc]; exact mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le

private lemma jacobian_control (A:ChartRatio G)(H:LocalRatio A){r:ℝ}
 (he:∀ y:G.Color,‖y‖≤r → 0≤A.J y ∧ A.J y ≤2):∃ B > 0, ∀ y:G.Color,‖y‖≤r → |A.J y-1|≤B*‖y‖:=by
 obtain ⟨c,hc,h⟩:= ((H.germ 0 (mem_ball_self H.patch)).differentiableAt (by simp)).hasFDerivAt.isBigO_sub.exists_pos
 obtain ⟨u,hu,hy⟩:= Metric.nhds_basis_closedBall.eventually_iff.1 h.bound
 refine ⟨max c (1/u),hc.trans_le (le_max_left ..),fun x hx=>?_⟩
 by_cases h' : ‖x‖ ≤ u
 · apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left c _) (norm_nonneg x)); simpa [Real.norm_eq_abs,H.anchored] using hy (show x∈closedBall (0:G.Color) u from mem_closedBall_zero_iff.mpr h')
 obtain ⟨s,t⟩:= he x hx
 calc
 |A.J x-1| ≤ 1:= abs_le.mpr (by constructor <;> linarith only [s,t])
 _ ≤ (1/u)*‖x‖:= by apply (show (1:ℝ)≤1/u*u from by rw [div_mul_cancel₀ _ hu.ne']).trans; exact mul_le_mul_of_nonneg_left (le_of_not_ge h') (by positivity)
 _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg x)

-- Compare on dim-scaled chart. Both exponents have a strictly negative **quadratic** upper bound;
-- no division by a k-dependent Gaussian inside a growing annulus.
private lemma jitter {κ r t D:ℝ} {x y:G.Color}
 (p:0<t)(q:0<κ)(hr:0<r)(hd:0<D)(h:t*‖y‖=‖x‖)(hy : ‖y‖≤r)
 (hj:‖y‖/2≤G.chord (G.lieExp y))(hw:|G.chord (G.lieExp y)-‖y‖| ≤ D*‖y‖^2) :
 let M:= κ/2 * (D*(2+D*r))
 let b:= -κ/8 * ‖x‖^2
 mouth G (κ*t^2) (G.lieExp y) ≤ Real.exp b ∧
 t * |mouth G (κ*t^2) (G.lieExp y)-Real.exp (-(κ/2)*‖x‖^2)|≤ M*(‖x‖^3*Real.exp b) := by
 intro M b; let w:= ‖y‖; let z:=G.chord (G.lieExp y)
 have ht: - (κ*t^2) * G.price (G.lieExp y) = - (κ/2)* (t*z)^2 := by rw [mul_pow,show z^2= _ from G.chord_price _]; ring
 rw [mouth,ht]
 have iu: -(κ/2) * ‖x‖^2 ≤ b:=by unfold b; nlinarith only [mul_nonneg q.le (sq_nonneg ‖x‖)]
 have it: -(κ/2) * (t*z)^2 ≤ b:=by
   unfold b; have hh:= pow_le_pow_left₀ (show 0 ≤ t*(‖y‖/2) by positivity) (mul_le_mul_of_nonneg_left (show _≤z from hj) p.le) 2
   rw [mul_div_assoc' t ‖y‖ 2,h] at hh -- lemma?
   nlinarith only [mul_le_mul_of_nonneg_left hh q.le]
 refine ⟨Real.exp_le_exp.mpr it,(mul_le_mul_of_nonneg_left (expo_lipschitz_top it iu) p.le).trans ?_⟩
 have h₁ : |(t*z)^2-‖x‖^2|≤ t^2 * ((D*w^2)*((2+D*r)*w)):=by
   have j:|z+w|≤ (2+D*r)*w:=by
     rw [abs_of_nonneg (add_nonneg (G.chord_nonneg _) (norm_nonneg _))]; change _ ≤ (2+D*r)*‖y‖
     change |z-‖y‖| ≤ _ at hw
     nlinarith only [(abs_le.mp hw).2,mul_le_mul_of_nonneg_right hy (show 0≤D*‖y‖ by positivity)]
   rw [←h,show (t*z)^2-(t*‖y‖)^2=t^2*((z-w)*(z+w)) from by unfold w; ring,abs_mul,abs_of_nonneg (sq_nonneg t),abs_mul]
   exact mul_le_mul_of_nonneg_left (mul_le_mul (show |z-w|≤ D*w^2 from hw) j (abs_nonneg _) (by positivity)) (sq_nonneg _)
 rw [← mul_sub,abs_mul,abs_neg,abs_of_pos (half_pos q)]
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ (half_pos q).le) (Real.exp_pos _).le) p.le).trans (le_of_eq ?_)
 unfold M w; rw [←h]; ring -- b changed?

private lemma perle_control (A:ChartRatio G)(H:LocalRatio A){r D κ:ℝ}
 (hr:0<r)(hd:0<D)(hk:0<κ)
 (he:∀ y:G.Color,‖y‖≤r → 0≤A.J y ∧ A.J y ≤2 ∧
      ‖y‖/2 ≤ G.chord (G.lieExp y) ∧ |G.chord (G.lieExp y)-‖y‖| ≤ D * ‖y‖^2):
 ∃ C>0,∀ t > (0:ℝ), t * |(∫ x:G.Color,perle A κ r t x)-narrow A κ| ≤ C := by
 let L := fun x:G.Color=> A.scale * Real.exp (-(κ/2)*‖x‖^2)
 have Lint: (∫ x,L x)=narrow A κ:=by unfold L narrow; rw [integral_const_mul,GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
 obtain ⟨B,hB,j⟩:=jacobian_control A H (fun y h'=> ⟨(he y h').1,(he y h').2.1⟩)
 let a:= κ/8; have ha:0 < a:=by unfold a; positivity
 let b:= fun x:G.Color=> Real.exp (-a*‖x‖^2); let c:=fun x:G.Color=>Real.exp (-(a/2)*‖x‖^2)
 obtain ⟨Q,hQ,q⟩:=boltz ha 3; obtain ⟨U,hU,u⟩:=boltz ha 1
 let M:= κ/2*(D*(2+D*r)); have hm: 0 ≤ M:=by unfold M; positivity
 let F(x:G.Color):= A.scale*(M*Q+B*U+U/r)*c x
 have hf:= H.scale; have hFp(x:G.Color):0≤F x:=by unfold F c; positivity
 have hg {k:ℝ}(h:0<k): Integrable (fun x:G.Color=> Real.exp (-k*‖x‖^2)):=by
   have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(k:ℂ)) (show 0 < k from h) 0 (0:G.Color)).norm
   simpa [Complex.norm_exp,pow_two,Complex.mul_re] using hg
 have hF:Integrable F:=(hg (half_pos ha)).const_mul _; have hL:Integrable L:=(hg (half_pos hk)).const_mul _
 refine ⟨(∫ x,F x) + 1,add_pos_of_nonneg_of_pos (integral_nonneg hFp) zero_lt_one,fun t ht=>?_⟩
 let f:=perle A κ r t
 have f0: Measurable f:=by
   have hv : Measurable (fun y : G.Color => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) := (measurable_const.mul H.borel).mul (((mouth_cont G _).comp G.lieExp_cont).measurable)
   exact ((hv.indicator isClosed_closedBall.measurableSet).comp (show Continuous (fun x : G.Color => t⁻¹ • x) from by fun_prop).measurable)
 have holds(x:G.Color): t*|f x-L x|≤F x:=by
   let y := t⁻¹ • x
   have hd0:t*‖y‖=‖x‖:=by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le]; field_simp
   have jp: ‖x‖*b x≤U*c x:=by simpa only [pow_one,b,c] using u ‖x‖ (norm_nonneg x)
   by_cases hy:y∈closedBall 0 r
   · rw [show f x=(A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y) from indicator_of_mem hy _];
     have hQy:‖y‖≤r:=mem_closedBall_zero_iff.mp hy
     let Y:= mouth G (κ*t^2) (G.lieExp y); let Z:=Real.exp (-(κ/2)*‖x‖^2)
     obtain ⟨h₁,h₂⟩ := jitter ht hk hr hd hd0 hQy (he y hQy).2.2.1 (he y hQy).2.2.2
     have s1:Y ≤ b x:=by simpa only [neg_div,Y,b,a] using h₁
     have s2: t*|Y-Z| ≤ M*(Q*c x):= by
       refine le_trans ?_ (mul_le_mul_of_nonneg_left (show ‖x‖^3*b x≤_ from q ‖x‖ (norm_nonneg _)) hm)
       simpa only [M,b,a, neg_div] using h₂
     have hi : t*(|A.J y-1| *Y) ≤ B*(U*c x):=by
       apply (mul_le_mul_of_nonneg_left (mul_le_mul (j y hQy) s1 (mouth_pos ..).le (mul_nonneg hB.le (norm_nonneg _))) ht.le).trans
       rw [show t*(B*‖y‖*b x)=B*((t*‖y‖)*b x) by ring,hd0]; exact mul_le_mul_of_nonneg_left jp hB.le
     change t*|A.scale*A.J y*Y-A.scale*Z|≤_
     rw [show A.scale*A.J y*Y-A.scale*Z=A.scale*((A.J y-1)*Y+(Y-Z)) by ring,abs_mul,abs_of_pos H.scale,show t*(A.scale*_) = A.scale*(t*|(A.J y-1)*Y+(Y-Z)|) by ring]
     unfold F; rw [mul_assoc]
     refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (abs_add_le ..) ht.le).trans ?_) H.scale.le
     rw [abs_mul,abs_of_pos (show 0<Y from Real.exp_pos _),mul_add]
     have h0:0≤ U/r*c x:=by unfold c; positivity
     nlinarith only [hi,s2,h0]
   rw [show f x=0 from indicator_of_notMem hy _,zero_sub,abs_neg,abs_of_nonneg (show 0≤L x from mul_nonneg hf.le (Real.exp_pos _).le)]
   have hw := le_of_lt (lt_of_not_ge (mt mem_closedBall_zero_iff.mpr hy))
   have hx : t * r ≤ ‖x‖:=by rw [← hd0]; exact mul_le_mul_of_nonneg_left hw ht.le
   have hv: L x≤ A.scale*b x:=by
     refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hf.le; unfold a; nlinarith only [mul_nonneg hk.le (sq_nonneg ‖x‖)]
   have hh : t*b x ≤ U/r*c x:=by
     have hg:0≤b x := (Real.exp_pos _).le
     apply le_of_mul_le_mul_left _ hr
     rw [show r*(U/r*c x) = U*c x from by field_simp]; nlinarith only [mul_le_mul_of_nonneg_right hx hg,jp]
   apply (mul_le_mul_of_nonneg_left hv ht.le).trans; unfold F; rw [mul_assoc A.scale]
   rw [mul_left_comm]; refine mul_le_mul_of_nonneg_left (hh.trans ?_) hf.le
   refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ?_) (Real.exp_pos _).le; positivity
 have h₁:Integrable (f - L) := (hF.const_mul (1/t)).mono' (f0.sub (show Continuous L by unfold L; fun_prop).measurable).aestronglyMeasurable (Eventually.of_forall fun x=>by -- fix
    rw [Pi.sub_apply,Real.norm_eq_abs,show (1/t)*F x= F x /t by ring]; apply (le_div_iff₀ ht).2; rw [mul_comm]; exact holds x)
 have h₂:Integrable f:= by simpa using h₁.add hL
 change t*|_ - _|≤_
 rw [← Lint,← integral_sub h₂ hL]
 apply le_trans _ (le_add_of_nonneg_right (by positivity : 0 ≤ (1:ℝ)))
 rw [show t*|∫ x:G.Color,f x-L x|=|t*(∫ x:G.Color,f x-L x)| from by rw [abs_mul,abs_of_pos ht],←integral_const_mul,← Real.norm_eq_abs] -- f
 exact norm_integral_le_of_norm_le hF (Eventually.of_forall fun x=>by rw [Real.norm_eq_abs,abs_mul,abs_of_pos ht]; exact holds x)

lemma cobalt_asymptotic (A:ChartRatio G)(H:LocalRatio A){κ:ℝ}(hk:0<κ):∃ K > 0, ∀ t≥(1:ℝ), t*|t^(Module.finrank ℝ G.Color)*linkZ G (κ*t^2)-narrow A κ| ≤ K:=by
 obtain ⟨r,ε,D,hr,hl,he,hD,hv,hu⟩ := kernel_ball A H
 obtain ⟨C,hC,v⟩:=perle_control A H hr hD hk hv; let d:=Module.finrank ℝ G.Color
 obtain ⟨Q,hQ,q⟩:=boltz (mul_pos hk he) (d+1)
 refine ⟨C+Q,add_pos hC hQ,fun t ht=>?_⟩
 have p:0<t:=zero_lt_one.trans_le ht
 let B:=(G.lieExp '' closedBall 0 r)ᶜ; have he' : MeasurableSet (G.lieExp '' closedBall 0 r) := ((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet
 let F:=mouth G (κ*t^2)
 have e : t^d*linkZ G (κ*t^2)= (∫ x, perle A κ r t x) + t^d*(∫ y in B,F y ∂ G.probHaar):=by
   unfold perle
   rw [Measure.integral_comp_inv_smul_of_nonneg volume (f:= (closedBall _ _).indicator _) p.le, smul_eq_mul, show Module.finrank ℝ G.Color=d from rfl,←mul_add]
   rw [integral_indicator isClosed_closedBall.measurableSet,← kernel_integral A H hl _ (mouth_cont G _).measurable,show (∫ y in B,F y ∂ G.probHaar)=_ from rfl] -- noop
   unfold F B; rw [integral_add_compl he' (mouth_int ..)]; rfl
 let Y:=Real.exp (-(κ*ε)*t^2)
 have Hp:= (pow_pos p d).le
 have hy(y:G.El)(hb:y∈B): F y ≤ Y:= by
   apply Real.exp_le_exp.mpr; nlinarith only [mul_le_mul_of_nonneg_left (hu y hb) (show 0≤κ*t^2 by positivity)]
 change t*|t^d*linkZ _ _-_| ≤ _
 rw [e,add_sub_right_comm]; apply (mul_le_mul_of_nonneg_left (abs_add_le ..) p.le).trans; rw [mul_add, abs_of_nonneg (mul_nonneg Hp (setIntegral_nonneg he'.compl fun y _=> (mouth_pos ..).le))]; apply add_le_add (v t p)
 have hY : t^(d+1) * Y ≤ Q:= le_trans (q t p.le) (mul_le_of_le_one_right hQ.le (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg (show 0≤κ*ε from (mul_pos hk he).le) (sq_nonneg t)]))) -- wrong Y: q bound with exp half fine
 rw [←mul_assoc, mul_comm t,←pow_succ]
 apply le_trans (mul_le_mul_of_nonneg_left _ (pow_nonneg p.le (d+1))) hY
 apply le_trans (setIntegral_mono_on (mouth_int G _).integrableOn integrableOn_const he'.compl hy)
 rw [setIntegral_const,smul_eq_mul]; exact mul_le_of_le_one_left (Real.exp_pos _).le (measureReal_le_one)
end YM.SectorNext.Vacuum
end
