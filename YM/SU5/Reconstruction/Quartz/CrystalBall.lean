import YM.SU5.Reconstruction.Quartz.Pele
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace
open Complex Ravin
lemma pressure_scale(c:ℝ)(x:Du) : pressure (c • x)=c^2*pressure x:=by simp [pressure];ring
lemma Largo_sub(t u:Du): Largo (t-u)= Largo t-Largo u:=by ext<;> simp[Largo]
lemma confection(b:ℝ)(R:Du)(F:Du→ℂ)(p:0<b): vat b (Largo R) F= ∫ x:Du, wallRate 1 x • F ((Real.sqrt b)⁻¹ • x + R):= by
 let t:= Real.sqrt b; have ht:0<t:=Real.sqrt_pos.2 p; have h:t^2=b:= Real.sq_sqrt p.le
 let f(x:Du):= Blaze b (Largo x-Largo R)*F x; change (∫ x, f x)=_
 rw [← integral_add_right_eq_self (μ:=volume) f R]; let g(x:Du):=f (x+R)
 have he: (∫ x:Du,g (t⁻¹ • x))= b • ∫ x:Du,g x:= by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume g ht.le, show Module.finrank ℝ Du=2 from (by rw[show Module.finrank ℝ Du= _ from Module.finrank_prod ..];simp),h] -- tune
 have hv(x:Du): Blaze b (Largo (t⁻¹ • x +R)- Largo R)= (b:ℂ)*↑(wallRate 1 x):= by
    rw[←Largo_sub,add_sub_cancel_right,blaze_land, ← Complex.ofReal_mul]; congr 1; unfold wallRate; rw [one_mul,pressure_scale,← mul_assoc (-b),inv_pow,h,neg_mul,mul_inv_cancel₀ p.ne']
 have hk(x:Du): g (t⁻¹ • x)= b • (wallRate 1 x • F (t⁻¹ • x+R)):= by unfold g f; rw [hv]; simp [Complex.real_smul,mul_assoc]
 apply (smul_right_injective ℂ p.ne'); change b • (∫ x:Du,g x)=b • (∫ x:Du, wallRate 1 x • F (t⁻¹ • x+R)); rw [←he,← integral_smul]; exact integral_congr_ae (ae_of_all _ hk) -- name
lemma festival (R:Du)(F:Du→ℂ)(B:ℝ)(p:Continuous F)(v:∀ x:Du,‖F x‖≤B):Tendsto (fun n:ℕ=> vat (sightParam n) (Largo R) F) atTop (𝓝 (Real.pi • F R)):= by
 let t(n:ℕ):= (Real.sqrt (sightParam n))⁻¹; have ht (x:Du): Tendsto (fun n=> t n • x+R) atTop (𝓝 R):= by
    let h:= tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)); simpa [t,sightParam] using (h.smul_const x).add_const R -- tune
 have he:= tendsto_integral_of_dominated_convergence (F:= fun n:ℕ=>fun x:Du=> wallRate 1 x • F (t n • x+R)) (μ:=volume) (f:=fun x:Du=> wallRate 1 x • F R) (fun x=>wallRate 1 x *B) (fun n=> (show Continuous (fun x:Du=>wallRate 1 x • F (t n • x+R)) by unfold wallRate pressure;fun_prop).aestronglyMeasurable) ((fullWarm 1 (by norm_num)).mul_const B) (fun n=> ae_of_all _ fun x=> (?_ : ‖_‖≤wallRate 1 x *B)) (ae_of_all _ (fun x=>Tendsto.const_smul (p.continuousAt.tendsto.comp (ht x)) _))
 · rw [integral_smul_const,costs _ zero_lt_one] at he; have hc(i:ℕ):0<sightParam i:=by unfold sightParam; positivity
   simp_rw [confection _ _ _ (hc _ )]; exact he
 rw [norm_smul, Real.norm_of_nonneg (rate_pos _ _ zero_lt_one).le]; gcongr; exacts [(rate_pos _ _ zero_lt_one).le,v _]
lemma windy(W t:Du):pressure (t-W) ≥ (pressure t)/2-pressure W:=by unfold pressure; simp only [Prod.fst_sub,Prod.snd_sub]; nlinarith [sq_nonneg (t.1-2*W.1),sq_nonneg (t.2-2*W.2)]
lemma magnet (b B:ℝ)(w:Ba)(p:0<b)(h: pressure (Forge w)+ pressure (Eddy w)≤B) (t:Du) : ‖Blaze b (Largo t-w)‖ ≤ 2*Real.exp (b*B)*wallRate (b/2) t:=by
 rw [toll p]; unfold wallRate; rw [show 2*_* (b/2 *Real.exp (-(b/2)*pressure t))= b*(Real.exp (b*B)*Real.exp (-(b/2)*pressure t)) from (by ring),mul_assoc,← Real.exp_add,← Real.exp_add]; gcongr b*Real.exp ?_; nlinarith [windy (Forge w) t]
-- continuum usability (cost can depend on x,d). Scalar.
lemma cucumber (b B a:ℝ)(w:ℂ→Ba)(F:ℂ→Du→ℂ)(p:0<b)(hw:Differentiable ℂ w)
  (v:∀z∈D, pressure (Forge (w z))+pressure (Eddy (w z))≤B) (hp:0≤ a)
  (m:∀ z∈D,AEStronglyMeasurable (F z) volume)(e:∀ z∈D,∀ t:Du, ‖F z t‖ ≤a)
  (c:∀ x:Du,ContinuousOn (fun z=> F z x) D)(d:∀ x:Du,DifferentiableOn ℂ (fun z=>F z x) Dw):
    let u(z:ℂ):= vat b (w z) (F z)
    ContinuousOn u D ∧ DifferentiableOn ℂ u Dw:= by
 intro u; let G(z:ℂ)(x:Du):=Blaze b (Largo x-w z)*F z x; let U(x:Du):=2*Real.exp (b*B)*wallRate (b/2) x*a
 have ht(z:ℂ)(h:z∈D): AEStronglyMeasurable (G z) volume:=(vat_score b _ p (F z) a hp (m z h) (e z h)).1.aestronglyMeasurable
 have hu : Integrable U:= ((fullWarm _ (half_pos p)).const_mul _).mul_const _
 have h(z)(g:z∈D)(x:Du):‖G z x‖≤ U x:= by unfold G U; rw[norm_mul]; exact mul_le_mul (magnet b B (w z) p (v z g) x) (e z g x) (norm_nonneg _) (by have h0:= rate_pos (b/2) x (half_pos p); positivity)
 have hb(x:Du): Differentiable ℂ (fun z=> Blaze b (Largo x-w z)):= by unfold Blaze; fun_prop
 have k : Dw⊆ D:= inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)
 constructor
 · intro z s; refine tendsto_integral_filter_of_dominated_convergence (l:=𝓝[D] z) U (Eventually.mono self_mem_nhdsWithin (fun y p=> ht y p)) (Eventually.mono self_mem_nhdsWithin fun y p=>ae_of_all _ (h y p)) hu ?_; exact ae_of_all _ fun t=> ((hb t).continuous.continuousOn.mul (c t)) z s
 intro z g; exact (ConePrice.Storm.averaging_hol G (isOpen_Ioo.reProdIm isOpen_Ioo) g hu (fun i v=> ht i (k v)) (fun i v=>h i (k v)) (fun x=>(hb x).differentiableOn.mul (d x))).differentiableWithinAt
end YM.Quartz.Waltz
