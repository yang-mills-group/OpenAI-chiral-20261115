/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SectorNext.VACUUM_NORMALIZATION.Laplace

/-!
# Quantitative charge per noise bond (not to be used to estimate uniform in volume without dilution)

Same calibration as first_asymptotic. Also helpers for global real chart calculations.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
set_option linter.unusedVariables false
noncomputable section
namespace YM.SectorNext.Vacuum
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations Metric
variable {G : Gauge}

lemma exp_deficit {a b:ℝ} (z:ℝ)(ha:a≤z)(hb:b≤z): |Real.exp a-Real.exp b|≤Real.exp z*|a-b|:=by
 have g{a b:ℝ}(h:b≤a)(t:a≤z):Real.exp a-Real.exp b≤Real.exp z*(a-b):=calc
    _ ≤ Real.exp a*(a-b) := by
      rw [show b=a+(b-a) by ring] -- all occurrences inc RHS; ring
      rw [Real.exp_add]
      nlinarith only [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_pos a).le]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_monotone t) (sub_nonneg.mpr h)
 rcases le_total a b with h|h
 · rw [abs_sub_comm (Real.exp a), abs_of_nonneg (sub_nonneg.mpr (Real.exp_monotone h)),abs_sub_comm a, abs_of_nonneg (sub_nonneg.mpr h)]; exact g h hb
 rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_monotone h)),abs_of_nonneg (sub_nonneg.mpr h)]; exact g h ha

lemma scale_through_pow_exp {a:ℝ} (ha:0<a)(d:ℕ) : Tendsto (fun t : ℝ => t^d*Real.exp (-t*a)) atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp (tendsto_id.atTop_mul_const ha)
    have ht : (fun t : ℝ => t^d*Real.exp (-t*a)) = fun t => (a^d)⁻¹ * (((id t)*a)^d*Real.exp (-(id t*a))) := by
      funext i; unfold id; rw [neg_mul,mul_pow]; field_simp
    rw [ht]
    simpa [Function.comp_def] using H.const_mul ((a^d)⁻¹)

lemma fire_integrable (G:Gauge){b:ℝ}(hb:0<b): Integrable (fun x:G.Color=> Real.exp (-b*‖x‖^2)) := by
    have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(b:ℂ))
      (show 0<b from hb) 0 (0:G.Color)).norm
    simpa [Complex.norm_exp,pow_two,Complex.mul_re] using hg
lemma bore_gauss (G:Gauge){b:ℝ}(hb:0<b)(d:ℕ) : Integrable (fun x:G.Color=> ‖x‖^d*Real.exp (-b*‖x‖^2)) := by
 let a:=b/2; have ha:0<a:=half_pos hb
 obtain ⟨X,H⟩:= eventually_atTop.mp ((scale_through_pow_exp ha d).eventually (ge_mem_nhds zero_lt_one))
 let C:=max 1 X
 have hx:1 ≤ C:= le_max_left ..
 have hU(t:ℝ)(ht:0≤t): t^d*Real.exp (-a*t^2)≤C^d:=by
   rcases le_total C t with p|p
   · have hv:t ≤ t^2:=by nlinarith [hx.trans p]
     refine le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht _)) ((H t ((le_max_right ..).trans p)).trans (one_le_pow₀ hx))
     exact Real.exp_monotone (by nlinarith only [ha,hv])
   exact le_trans (mul_le_of_le_one_right (pow_nonneg ht _) (Real.exp_le_one_iff.mpr (by nlinarith only [ha,sq_nonneg t]))) (pow_le_pow_left₀ ht p _)
 apply ((fire_integrable G ha).const_mul (C^d)).mono (Continuous.aestronglyMeasurable (by fun_prop))
 filter_upwards with x
 rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
 calc
    _= (‖x‖^d*Real.exp (-a*‖x‖^2))* Real.exp (-a*‖x‖^2) := by rw [mul_assoc,←Real.exp_add]; unfold a; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_right (hU _ (norm_nonneg _)) (Real.exp_pos _).le

/-- Keep this scale at the actual chart; cannot renormalize the Haar term separately. -/
lemma ratio_measure_near {G:Gauge}(A:ChartRatio G) (H:LocalRatio A):∃ L> (0:ℝ), ∃ R> (0:ℝ),∀ x:G.Color, ‖x‖≤R→ |A.J x-1| ≤ L*‖x‖:=by
 have h: DifferentiableAt ℝ A.J 0 := (H.germ 0 (Metric.mem_ball_self H.patch)).differentiableAt (by simp)
 obtain ⟨L,h0⟩:= h.hasFDerivAt.isBigO_sub.exists_nonneg
 obtain ⟨v,g⟩:=h0
 obtain ⟨R,r,Gk⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp g.bound
 refine ⟨1+L,by linarith,R,r,fun x p=>?_⟩; rw [←H.anchored,← Real.norm_eq_abs]; exact le_trans (by simpa only [sub_zero] using Gk (x:=x) (Metric.mem_closedBall.mpr (show dist x 0≤R by simpa using p))) (show L*‖x‖≤_ from mul_le_mul_of_nonneg_right (by linarith [H.anchored]) (norm_nonneg x))

private abbrev d₅ (G:Gauge):=Module.finrank ℝ G.Color
private def drink (A : ChartRatio G) (κ r t : ℝ) (x : G.Color) :=
  (closedBall 0 r).indicator (fun y => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) (t⁻¹ • x)
private lemma near_drink (A : ChartRatio G) (H : LocalRatio A) {κ r D : ℝ} (hk : 0<κ) (hr : 0<r)(hd:0<D)
    (he : ∀ x : G.Color, ‖x‖ ≤ r → 0 ≤ A.J x ∧ A.J x ≤ 2 ∧ ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ |G.chord (G.lieExp x)-‖x‖| ≤ D * ‖x‖^2) :
    ∃ C> (0:ℝ), ∀ t> (0:ℝ), |(∫ x,drink A κ r t x) - narrow A κ| ≤ C/t := by
 let a := κ/2; let b:=κ/8
 have ha:0<a:=by unfold a; positivity
 have hb:0<b:=by unfold b; positivity
 have hba:b≤a:=by unfold b a; linarith
 obtain ⟨L,hL,R,hR,K⟩:=ratio_measure_near A H
 let M:= L+1/R+1/r
 have hM:0<M:=by unfold M; positivity
 have kM{x:G.Color}(h:‖x‖≤r): |A.J x-1|≤M*‖x‖:=by
    rcases le_total ‖x‖ R with t|t
    · exact le_trans (K x t) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)|>.trans (le_add_of_nonneg_right (by positivity))) (norm_nonneg x))
    obtain ⟨G,G',_⟩:=he x h; refine le_trans (show |A.J x-1|≤1 by rw [abs_le]; constructor <;> linarith) ?_
    calc (1:ℝ)= (1/R)*R:=by field_simp
         _ ≤ _:= mul_le_mul (show 1/R≤M from (le_add_of_nonneg_left hL.le).trans (le_add_of_nonneg_right (by positivity))) t hR.le hM.le
 let U:= a*(2+D*r)*D
 have hU: 0<U:= by unfold U; positivity
 let P:= fun x:G.Color=> ‖x‖*Real.exp (-b*‖x‖^2)
 let Q:= fun x:G.Color=> ‖x‖^3*Real.exp (-b*‖x‖^2)
 let W:= fun x:G.Color=> M* P x+ U* Q x
 let F:=fun x:G.Color=> A.scale * Real.exp (-a*‖x‖^2)
 have hW x: 0≤ W x:=by unfold W P Q; positivity
 have vW: Integrable W:= ((show Integrable P from (by simpa only [pow_one] using bore_gauss G hb 1)).const_mul M).add ((bore_gauss G hb 3).const_mul U)
 have vF: Integrable F:= (fire_integrable G ha).const_mul _
 let C:= A.scale*(∫ x,W x)
 have vC:0≤C:=mul_nonneg H.scale.le (integral_nonneg hW)
 refine ⟨1+C,by linarith,fun t ht=>?_⟩
 have h x : |drink A κ r t x-F x|≤ (A.scale/t) * W x:=by
    let y:= t⁻¹ • x; let X:= ‖x‖; let Y:= ‖y‖; let z:= G.chord (G.lieExp y)
    have hx:0≤X:= norm_nonneg _; have hz:0≤z:=G.chord_nonneg _
    have Hn : t*Y=X := by unfold Y X y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le]; field_simp
    have Hy :Y=X/t:=eq_div_of_mul_eq ht.ne' (by rw [mul_comm,Hn])
    let F₀:= Real.exp (-a*X^2); let Fb:= Real.exp (-b*X^2)
    have vFb:0<Fb:= Real.exp_pos _
    have fbase:F₀ ≤ Fb:=Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hba) (sq_nonneg _))
    have ZW : W x=(M*X+U*X^3)*Fb:=by unfold W P Q Fb X; ring
    unfold drink; rcases le_or_gt Y r with p|p
    · obtain ⟨j0,j2,hl,hz'⟩:=he y p; rw [indicator_of_mem (a:=t⁻¹ • x) (Metric.mem_closedBall.mpr (show dist (t⁻¹ • x) 0≤r by simpa only [dist_zero_right] using p))]; let F₁:= Real.exp (-a*(t*z)^2)
      change |(A.scale*A.J y)*mouth _ _ _ - F x|≤_
      rw [show mouth _ _ _= F₁ from ?_]
      · have hu:z≤ (1+D*r)*Y:=by change |z-Y|≤ D*Y^2 at hz'; nlinarith only [(abs_le.mp hz').2,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p (norm_nonneg y)) hd.le]
        have hX: X/2≤ t*z:=by linarith only [Hn,mul_le_mul_of_nonneg_left (show Y/2≤z from hl) ht.le]
        have hY: |t*z-X|≤ D/t*X^2:=by
          rw [←Hn,←mul_sub,abs_mul,abs_of_pos ht]; exact (mul_le_mul_of_nonneg_left hz' ht.le).trans_eq (by change t*(D*Y^2)=_; field_simp)
        have hZ: |t*z+X|≤ (2+D*r)*X:= by
          rw [abs_of_nonneg (by positivity)]; rw [←Hn]; nlinarith only [mul_le_mul_of_nonneg_left hu ht.le]
        have he: -a*(t*z)^2 ≤ -b*X^2:=by
          unfold a b at *; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hX 2) hk.le]
        have heF: F₁≤Fb:= Real.exp_monotone he
        have e0:= (exp_deficit (-b*X^2) he (mul_le_mul_of_nonneg_right (neg_le_neg hba) (sq_nonneg X)))
        have hv : |F₁-F₀| ≤ U/t*X^3*Fb:=calc
          _ ≤ _ := e0
          _ = Fb*(a*(|t*z-X| * |t*z+X|)):=by rw [show -a*_ - -a*_ = -a*((t*z-X)*(t*z+X)) from by ring,abs_mul,abs_neg,abs_of_pos ha,abs_mul]
          _ ≤ Fb*(a*(D/t*X^2*((2+D*r)*X))):= by gcongr
          _ = _:=by unfold U; ring
        calc
          _ = A.scale * |(A.J y-1)* F₁+(F₁-F₀)|:=by rw [show F x=A.scale*F₀ from rfl,←abs_of_pos H.scale,←abs_mul,abs_of_pos H.scale];
                                                                         ring_nf
          _ ≤ _:=by
             apply (mul_le_mul_of_nonneg_left (abs_add_le ..) H.scale.le).trans; rw [abs_mul,abs_of_pos (show 0<F₁ from Real.exp_pos _)]
             refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul (kM p) heF (Real.exp_pos _).le (by positivity)) hv) H.scale.le).trans_eq ?_
             rw [ZW,show ‖y‖=X/t from Hy]; ring
      change Real.exp (- (κ*t^2)* G.price (G.lieExp y)) = F₁
      unfold F₁ z a; rw [mul_pow,G.chord_price]; ring_nf
    rw [indicator_of_notMem (a:=t⁻¹ • x) (show t⁻¹ • x∉closedBall 0 r from by simpa only [mem_closedBall,dist_zero_right,not_le] using p), zero_sub,abs_neg,abs_of_nonneg (show 0≤F x from mul_nonneg H.scale.le (Real.exp_pos _).le)]
    calc
      _ ≤ A.scale * Fb:= mul_le_mul_of_nonneg_left fbase H.scale.le
      _ ≤ A.scale/t * (M*X*Fb):=by
         have ht' : t≤ M*X:= calc t=1/r*(r*t):=by field_simp
                                    _ ≤ M*X := by
                                      apply mul_le_mul (le_trans (le_add_of_nonneg_left (show 0≤L+1/R by positivity)) le_rfl) ?_ (by positivity) hM.le
                                      linarith only [(lt_div_iff₀ ht).mp (show r<X/t from Hy ▸ p)]
         calc _ = A.scale/t*(t*Fb):= by field_simp
              _ ≤ _:= by have v:= H.scale; gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (show M*X*Fb≤_ by rw [ZW]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) vFb.le) (div_nonneg H.scale.le ht.le)
 have hm : Measurable (drink A κ r t) := by
    have hv : Measurable (fun y : G.Color => (A.scale*A.J y)*mouth G (κ*t^2) (G.lieExp y)) := (measurable_const.mul H.borel).mul (((mouth_cont G _).comp G.lieExp_cont).measurable)
    exact (hv.indicator Metric.isClosed_closedBall.measurableSet).comp (show Continuous (fun x : G.Color => t⁻¹ • x) from by fun_prop).measurable
 let G'(x):= drink A κ r t x-F x
 let M'(x):= (A.scale/t)*W x
 have ha' x:0≤ M' x:= mul_nonneg (div_nonneg H.scale.le ht.le) (hW _)
 have hv: Integrable M':= vW.const_mul _
 have hf: Integrable G' := hv.mono' (hm.aestronglyMeasurable.sub vF.aestronglyMeasurable) (Eventually.of_forall h)
 have hw:Integrable (drink A κ r t):=(show G'+F= _ from sub_add_cancel ..) ▸ (hf.add vF)
 rw [show narrow A κ = ∫ x,F x from ?_,← integral_sub hw vF]
 · rw [← Real.norm_eq_abs]; exact le_trans ((norm_integral_le_integral_norm G').trans (integral_mono hf.norm hv h)) (by unfold M'; rw [integral_const_mul]; calc _= C/t:=by unfold C; ring
                                                                                                                                                                       _ ≤ _:=by gcongr; linarith)
 unfold F narrow; rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ha]

private theorem calmExterior (A : ChartRatio G) (_ : LocalRatio A) {r ε κ : ℝ} (_ : 0<r) (_ : r<A.radius) (he : 0<ε) (hk : 0<κ)
    (hv : ∀ y : G.El,y∉G.lieExp '' closedBall 0 r → ε ≤ G.price y) :
    Tendsto (fun t : ℝ => t^(d₅ G + 1) * (∫ y in (G.lieExp '' closedBall 0 r)ᶜ,mouth G (κ*t^2) y ∂G.probHaar)) atTop (𝓝 0) := by
  let B := (G.lieExp '' closedBall 0 r)ᶜ
  have he' : MeasurableSet B := ((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet.compl
  let a := κ*ε
  have ha : 0<a := mul_pos hk he
  have hh : Tendsto (fun t : ℝ => t ^ (d₅ G + 1) * Real.exp (-t*a)) atTop (𝓝 0) := by
    have H := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero ((d₅ G + 1))).comp (tendsto_id.atTop_mul_const ha)
    have ht : (fun t : ℝ => t^(d₅ G + 1)*Real.exp (-t*a)) = fun t => (a^(d₅ G + 1))⁻¹ * (((id t)*a)^(d₅ G + 1)*Real.exp (-(id t*a))) := by
      funext i; unfold id; rw [neg_mul,mul_pow]; field_simp; unfold a; ring
    rw [ht]
    simpa [Function.comp_def] using H.const_mul ((a^(d₅ G + 1))⁻¹)
  apply squeeze_zero' _ _ hh
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (pow_nonneg ht _) (setIntegral_nonneg he' fun y _ => (mouth_pos _ _ _).le)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
  have hy (y : G.El) (hyi : y∈B) : mouth G (κ*t^2) y ≤ Real.exp (-t*a) := by
    apply Real.exp_le_exp.mpr
    have hI := hv y hyi
    have hj : t*ε ≤ t^2*G.price y := mul_le_mul (by nlinarith) hI he.le (by positivity : 0≤t^2)
    unfold a
    nlinarith only [mul_le_mul_of_nonneg_left hj hk.le]
  apply le_trans (setIntegral_mono_on (μ:=G.probHaar) (mouth_int G _).integrableOn (integrableOn_const) he' hy)
  rw [setIntegral_const, smul_eq_mul]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (by simp [measureReal_le_one])

theorem first_laplace_charge (A : ChartRatio G) (H : LocalRatio A) (κ : ℝ) (hk : 0<κ) :
    ∃ L> (0:ℝ), ∀ᶠ t:ℝ in atTop, |t^Module.finrank ℝ G.Color * linkZ G (κ*t^2)- narrow A κ| ≤ L/t := by
 obtain ⟨r,ε,D,hr,hl,he,hD,hv,hu⟩ := kernel_ball A H
 obtain ⟨C,v,F⟩:= near_drink A H hk hr hD hv
 let S:= G.lieExp '' closedBall 0 r
 have hS: MeasurableSet S:=((ProperSpace.isCompact_closedBall _ _).image G.lieExp_cont).measurableSet
 refine ⟨C+1,by linarith,?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ), (calmExterior A H hr hl he hk hu).eventually (ge_mem_nhds zero_lt_one)] with t ht h
 let a:= ∫ y in Sᶜ,mouth G (κ*t^2) y ∂G.probHaar; let m:= d₅ G
 let u:= t^m*a
 have hh: u≤1/t:= (le_div_iff₀ ht).mpr (by change t^(m+1)*a≤1 at h; rw [pow_succ,mul_right_comm] at h; exact h)
 have y:0≤u:=mul_nonneg (pow_nonneg ht.le _) (setIntegral_nonneg hS.compl (fun y _=> (mouth_pos ..).le))
 have f: t^Module.finrank ℝ G.Color * linkZ G (κ*t^2)- narrow A κ= ((∫ x,drink A κ r t x) -narrow A κ)+u:=by
    rw [sub_add_eq_add_sub]; congr 1
    unfold drink; rw [Measure.integral_comp_inv_smul_of_nonneg volume (f:= (closedBall _ _).indicator _) ht.le, smul_eq_mul]; unfold u m d₅ a; rw [←mul_add]
    rw [integral_indicator isClosed_closedBall.measurableSet,← kernel_integral A H hl _ (mouth_cont G _).measurable,integral_add_compl hS (mouth_int G _)]
    rfl
 rw [f,add_div]; exact (abs_add_le ..).trans (add_le_add (F t ht) ((abs_of_nonneg y).le.trans hh))

lemma log_charge {a b L:ℝ}(h:0<L)(ha:L≤a)(hb:L≤b): |Real.log a-Real.log b| ≤ |a-b|/L:=by
 have g{a b:ℝ}(v:L≤b)(t:b≤a):Real.log a-Real.log b≤(a-b)/L:=by
    have hp:0<b:= h.trans_le v; rw [←Real.log_div (hp.trans_le t).ne' hp.ne']; calc
       _ ≤ _ := Real.log_le_sub_one_of_pos (div_pos (hp.trans_le t) hp)
       _ = (a-b)/b := by field_simp
       _ ≤ (a-b)/L:= by gcongr
 rcases le_total a b with t|t
 · rw [abs_sub_comm (Real.log a), abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (h.trans_le ha) t)), abs_sub_comm a, abs_of_nonneg (sub_nonneg.mpr t)]; exact g ha t
 rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (h.trans_le hb) t)),abs_of_nonneg (sub_nonneg.mpr t)]; exact g hb t

lemma first_laplace_receipt (A : ChartRatio G) (H : LocalRatio A) (κ : ℝ) (hk : 0<κ) :
    ∃ L> (0:ℝ), ∀ᶠ t:ℝ in atTop, |Real.log (t^Module.finrank ℝ G.Color *linkZ G (κ*t^2))- Real.log (narrow A κ)| ≤ L/t:= by
 let z:= narrow A κ/2
 have hp:0< z:= half_pos (narrow_pos A H κ hk); have hh:z<narrow A κ:=half_lt_self (narrow_pos A H κ hk)
 obtain ⟨L,h,F⟩:=first_laplace_charge A H κ hk
 refine ⟨L/z,div_pos h hp, ?_⟩; filter_upwards [F,(first_asymptotic A H κ hk).eventually (le_mem_nhds hh)] with t f hf
 exact le_trans (log_charge hp hf hh.le) ((div_le_div_of_nonneg_right f hp.le).trans_eq (by ring))

end YM.SectorNext.Vacuum
#print axioms YM.SectorNext.Vacuum.first_laplace_receipt
