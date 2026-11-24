import Refrain.Kernel

set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Metric
variable {G:Gauge}
private def bulb (A:ChartRatio G) (κ r t: ℝ)(x:G.Color) := (closedBall 0 r).indicator (fun y=>(A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) (t⁻¹• x)
abbrev chargeF (A:ChartRatio G)(κ:ℝ)(x:G.Color) := A.scale*frost (κ/2) x
private lemma bulb_point (A:ChartRatio G)(H:LocalRatio A){κ r D C t:ℝ}(p:0<κ)(u:0<r)(h:0<t)(g:0<D)(he:0<C)(x:G.Color){f:G.El}(hp:G.chord f≥ (t⁻¹*‖x‖)/2)(hq:|G.chord f-(t⁻¹*‖x‖)| ≤ D*(t⁻¹*‖x‖)^2)(ht:t⁻¹*‖x‖≤r){J:ℝ}(hd:|J-1|≤C*(t⁻¹*‖x‖)) : |(A.scale*J)*mouth G (κ*t^2) f-chargeF A κ x| ≤ t⁻¹*A.scale*(C*‖x‖+κ*D*(2+D*r)*‖x‖^3)*frost (κ/8) x:=by
 let n:= ‖x‖
 have hn:0≤n:=norm_nonneg x
 let b:=G.chord f
 let y:=t*b
 let q:=t⁻¹*n
 have hv:0≤q:=mul_nonneg (inv_pos.mpr h).le hn
 have hy:t*q=n:=by unfold q; field_simp
 have hx : n/2 ≤ y:=by unfold y; linarith only [mul_le_mul_of_nonneg_left hp h.le, hy] -- defeq n?
 have hk: |y-n| ≤ D*t⁻¹*n^2:=by
    have hm: y-n=t*(b-q):= by rw [mul_sub,hy]
    rw [hm,abs_mul,abs_of_pos h]; exact (mul_le_mul_of_nonneg_left hq h.le).trans_eq (by change t*(D*q^2)=_; unfold q; field_simp)
 have hM:y+n≤ (2+D*r)*n:=by
    have hq':q≤r:= ht
    have hs:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' g.le) hn; unfold q at hs; nlinarith only [hs,(abs_le.mp hk).2]
 have hy':0≤y:=by linarith only [hn,hx]
 have hd' : |y^2-n^2|≤D*(2+D*r)*t⁻¹*n^3:=by
    rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hy' hn)]; exact (mul_le_mul hM hk (abs_nonneg _) (by have h':0<t⁻¹:=inv_pos.mpr h; positivity)).trans_eq (by ring) -- sq_sub_sq order
 let a:= κ/2
 have ha:0<a:=half_pos p
 have hc : mouth G (κ*t^2) f = Real.exp (-a*y^2):=by unfold mouth a y b; rw [mul_pow,G.chord_price]; ring_nf
 have hc' : frost (κ/2) x = Real.exp (-a*n^2):= rfl
 let E:=frost (κ/8) x
 have hS: Real.exp (-a*y^2)≤E:=Real.exp_le_exp.mpr (by change -a*y^2 ≤ -(κ/8)*n^2; unfold a; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hn]:0≤n/2) hx 2) p.le])
 have hS': frost (κ/2) x≤E:=Real.exp_le_exp.mpr (by change -(κ/2)*n^2≤-(κ/8)*n^2; nlinarith only [mul_nonneg p.le (sq_nonneg n)])
 have hm: |mouth G (κ*t^2) f-frost (κ/2) x|≤ E*κ*D*(2+D*r)*t⁻¹*n^3:=by
    rw [hc,hc']; have he:= exp_abs_lane (-a*y^2) (-a*n^2); rw [←mul_sub,abs_mul,abs_neg,abs_of_pos ha] at he; refine he.trans ((mul_le_mul (add_le_add hS hS') (mul_le_mul_of_nonneg_left hd' ha.le) (by positivity) (by unfold E frost; positivity)).trans_eq ?_); unfold a; ring
 have hv : |J*mouth G (κ*t^2) f-frost (κ/2) x| ≤ t⁻¹*(C*n+κ*D*(2+D*r)*n^3)*E:=by
    let z:= mouth G (κ*t^2) f
    change |J*z-_|≤ _
    rw [show J*z-frost (κ/2) x=(J-1)*z+(z-frost (κ/2) x) from by ring]
    have hz:0<z:=mouth_pos ..
    have hs:z≤E:=hc.trans_le hS
    refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_of_pos hz]
    exact (add_le_add (mul_le_mul hd hs hz.le ((abs_nonneg _).trans hd)) hm).trans_eq (by unfold n; ring)
 have hv':= mul_le_mul_of_nonneg_left hv H.scale.le
 unfold chargeF; rw [mul_assoc,←mul_sub,abs_mul,abs_of_pos H.scale]
 exact hv'.trans_eq (by ring) -- n E

private abbrev funding (A:ChartRatio G)(κ D C:ℝ)(r:ℝ) (x:G.Color) := A.scale*((C+r⁻¹)*‖x‖+κ*D*(2+D*r)*‖x‖^3)*frost (κ/8) x
private lemma bulb_pays (A:ChartRatio G)(H:LocalRatio A){κ r D C t:ℝ}(p:0<κ)(u:0<r)(h:0<t)(g:0<D)(he:0<C)(hf:∀ x:G.Color,‖x‖≤r → (‖x‖/2 ≤ G.chord (G.lieExp x) ∧ |G.chord (G.lieExp x)-‖x‖|≤D*‖x‖^2) ∧ |A.J x-1| ≤ C*‖x‖)(x:G.Color) : |bulb A κ r t x-chargeF A κ x|≤ t⁻¹*funding A κ D C r x:=by
 let n:= ‖x‖
 let y:=t⁻¹ • x
 have ht: ‖y‖=t⁻¹*‖x‖:=by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr h).le]
 have hv:0<t⁻¹:=inv_pos.mpr h
 by_cases hB:y∈closedBall 0 r
 · unfold bulb; rw [indicator_of_mem (show t⁻¹ • x∈closedBall 0 r from hB)]
   have hz:‖y‖≤r:=by simpa only [mem_closedBall,dist_zero_right] using hB
   obtain ⟨⟨hy,hq⟩,hk⟩:=hf y hz
   rw [ht] at hy hk hq hz
   apply le_trans (bulb_point A H p u h g he x hy hq hz hk)
   unfold funding frost; rw [←mul_assoc t⁻¹,←mul_assoc t⁻¹]; have hs:=H.scale; gcongr; all_goals first | assumption | positivity | exact le_add_of_nonneg_right (inv_pos.mpr u).le -- rw order?
 unfold bulb chargeF; rw [indicator_of_notMem (show t⁻¹ • x∉closedBall 0 r from hB),zero_sub,abs_neg,abs_of_pos (mul_pos H.scale (Real.exp_pos _))]; have hz:r≤t⁻¹*‖x‖:=(le_of_lt (lt_of_not_ge (by intro v; apply hB; rwa [mem_closedBall,dist_zero_right,ht])))
 have hm:frost (κ/2) x≤frost (κ/8) x:=Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg p.le (sq_nonneg ‖x‖)]) -- unfold wrong
 refine (mul_le_mul_of_nonneg_left hm H.scale.le).trans ?_; unfold funding; rw [←mul_assoc t⁻¹]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
 have hy: (1:ℝ)≤ t⁻¹*(r⁻¹*‖x‖):=by have hi:=mul_le_mul_of_nonneg_left hz (inv_pos.mpr u).le; rw [inv_mul_cancel₀ u.ne'] at hi; linarith only [hi]
 calc
    _ = A.scale *1:= by rw [mul_one]
    _ ≤ A.scale*(t⁻¹*(r⁻¹*‖x‖)):=mul_le_mul_of_nonneg_left hy H.scale.le
    _ ≤ _ := by rw [show t⁻¹*(A.scale*((C+r⁻¹)*‖x‖+κ*D*(2+D*r)*‖x‖^3))= A.scale*(t⁻¹*((C+r⁻¹)*‖x‖+κ*D*(2+D*r)*‖x‖^3)) from by ring]; have hS:=H.scale; gcongr; all_goals first | assumption | positivity | exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left he.le) (norm_nonneg x)).trans (le_add_of_nonneg_right (by positivity : 0≤κ*D*(2+D*r)*‖x‖^3))
private lemma bulb_invoice (A:ChartRatio G)(H:LocalRatio A){κ r D:ℝ}(p:0<κ)(u:0<r)(m:r<A.radius)(g:0<D)(hf:∀ x:G.Color,‖x‖≤r → ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ |G.chord (G.lieExp x)-‖x‖|≤D*‖x‖^2) :∃ C:ℝ,∀ t> (0:ℝ), |(∫ x,bulb A κ r t x)-narrow A κ| ≤ C/t:=by
 obtain ⟨C,he,hC⟩:=Jacob_linear A H m u.le
 let F:= funding A κ D C r
 have hm: Integrable F:=by
    let E:=frost (G:=G) (κ/8)
    have hκ:0<κ/8:=by positivity
    have h0: F=fun x:G.Color=> A.scale*((C+r⁻¹)*(‖x‖^1*E x)+(κ*D*(2+D*r))*(‖x‖^3*E x)):=by funext x; unfold F E funding; ring
    rw [h0]; exact (((tint_grow 1 hκ).const_mul (C+r⁻¹) |>.add ((tint_grow 3 hκ).const_mul (κ*D*(2+D*r)))).const_mul A.scale)
 refine ⟨∫ x,F x,fun t h=>?_⟩
 let L:=chargeF A κ
 have hg:Integrable L:= (tint_frost (half_pos p)).const_mul A.scale
 have hbf (x:G.Color): ‖bulb A κ r t x-L x‖≤ t⁻¹*F x:= bulb_pays A H p u h g he (fun x w=>⟨hf x w,hC x w⟩) x
 have hx : AEStronglyMeasurable (bulb A κ r t):=by
    unfold bulb
    have hv : Measurable (fun y : G.Color => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) := (measurable_const.mul H.borel).mul (((mouth_cont G _).comp G.lieExp_cont).measurable)
    exact (((hv.indicator isClosed_closedBall.measurableSet).comp (show Continuous (fun x : G.Color => t⁻¹ • x) from by fun_prop).measurable).aestronglyMeasurable)
 have hr:Integrable (fun x=>bulb A κ r t x-L x):= (hm.const_mul t⁻¹).mono (hx.sub hg.1) (Eventually.of_forall (fun x=> (hbf x).trans (le_abs_self _)))
 have hh : (∫ x,L x)=narrow A κ:=by unfold narrow L chargeF frost; rw [integral_const_mul,GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)] -- unfold order
 have hb:Integrable (bulb A κ r t):=by convert! hr.add hg using 1; ext x; simp
 rw [←hh, ← integral_sub hb hg]
 refine (norm_integral_le_integral_norm (μ:=volume) (fun x:G.Color=>bulb A κ r t x-L x)).trans ?_; exact (integral_mono hr.norm (hm.const_mul t⁻¹) hbf).trans_eq (by rw [integral_const_mul]; ring)
lemma tail_faster (n:ℕ){ε:ℝ}(p:0<ε) : Tendsto (fun t:ℝ=> t^n*Real.exp (-ε*t)) atTop (𝓝 0):=by
 have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (tendsto_id.atTop_mul_const p)
 have h: (fun t:ℝ=>t^n*Real.exp (-ε*t))= fun t=>(ε^n)⁻¹*((id t*ε)^n*Real.exp (-(id t*ε))):=by
    funext t; unfold id; rw [neg_mul, mul_pow,mul_comm t ε]; field_simp
 rw [h]; simpa [Function.comp_def] using H.const_mul ((ε^n)⁻¹)
lemma toll_sharp (A:ChartRatio G)(H:LocalRatio A){κ:ℝ}(p:0<κ):∃ C> (0:ℝ),∀ᶠ t:ℝ in atTop, |t^ Module.finrank ℝ G.Color*linkZ G (κ*t^2)-narrow A κ| ≤ C/t:=by
 obtain ⟨r,ε,D,hr,hR,he,hD,hg,hf⟩:=kernel_ball A H
 obtain ⟨C,hC⟩:= bulb_invoice A H p hr hR hD (fun x h=> (hg x h).2.2)
 let B:=G.lieExp '' closedBall (0:G.Color) r
 let n:=Module.finrank ℝ G.Color
 have hm:MeasurableSet B:=((ProperSpace.isCompact_closedBall _ r).image G.lieExp_cont).measurableSet
 let a:=κ*ε
 have hp:0<a:=mul_pos p he
 refine ⟨|C|+1,by positivity,?_⟩
 filter_upwards [eventually_ge_atTop (1:ℝ),(tail_faster (n+1) hp).eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with t h h0
 let f:=mouth G (κ*t^2)
 let X:=∫ y in Bᶜ,f y ∂G.probHaar
 have hX:0≤X:= setIntegral_nonneg hm.compl (fun y _=> (Real.exp_pos _).le)
 have ht:0<t:=zero_lt_one.trans_le h
 have h':(∫ x,bulb A κ r t x)+t^n*X=t^ Module.finrank ℝ G.Color*linkZ G (κ*t^2):= by
    unfold bulb X B n f
    rw [Measure.integral_comp_inv_smul_of_nonneg volume (f:= (closedBall _ _).indicator _) ht.le, smul_eq_mul,←mul_add]
    rw [integral_indicator isClosed_closedBall.measurableSet,← kernel_integral A H hR _ (mouth_cont G _).measurable,integral_add_compl hm (mouth_int G _)]
    rfl
 have hy (y : G.El) (hyi : y∈Bᶜ) : f y ≤ Real.exp (-a*t) := by
    apply Real.exp_le_exp.mpr
    have hI := hf y hyi
    have hj : t*ε ≤ t^2*G.price y := mul_le_mul (by nlinarith) hI he.le (by positivity : 0≤t^2)
    unfold a
    nlinarith only [mul_le_mul_of_nonneg_left hj p.le]
 have hh:X≤Real.exp (-a*t):=by
    apply le_trans (setIntegral_mono_on (μ:=G.probHaar) (mouth_int G _).integrableOn (integrableOn_const) hm.compl hy)
    rw [setIntegral_const, smul_eq_mul]; exact mul_le_of_le_one_left (Real.exp_pos _).le (by simp [measureReal_le_one])
 rw [← h',add_sub_right_comm]
 refine (abs_add_le ..).trans ?_; rw [add_div,abs_of_nonneg (mul_nonneg (pow_nonneg ht.le _) hX)]
 refine add_le_add ((hC t ht).trans (div_le_div_of_nonneg_right (le_abs_self _) ht.le)) ((mul_le_mul_of_nonneg_left hh (pow_nonneg ht.le _)).trans ((le_div_iff₀ ht).mpr ?_))
 change t^(n+1)*Real.exp (-a*t)≤1 at h0; rw [pow_succ] at h0; linarith only [h0]
end YM.SectorNext.Vacuum
