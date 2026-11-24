import YM.SU5.Thin.Press.Lance
import YM.SU5.Thin.Press.Lilt
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Sleigh
open Filter Function Set Lattice RG Wilson Pressure Precision MeasureTheory SectorNext.Vacuum
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
open Next.Fluctuations Metric
variable {G:Gauge}{A:ChartRatio G}(H:LocalRatio A){r D κ:ℝ}
include H
abbrev dim (G:Gauge):= Module.finrank ℝ G.Color
lemma fiord_earned (hr:0<r)(hw:r<A.radius)(hD:0<D)(v:0<κ)
    (U:∀ x : G.Color, ‖x‖ ≤ r → 0 ≤ A.J x ∧ A.J x ≤ 2 ∧ ‖x‖/2 ≤ G.chord (G.lieExp x) ∧ |G.chord (G.lieExp x)-‖x‖| ≤ D * ‖x‖^2):
 Paddled (-1) (fun t => t^dim G * (∫ y in G.lieExp '' closedBall 0 r,mouth G (κ*t^2) y ∂G.probHaar)-narrow A κ):= by
 obtain ⟨C,c,hc⟩:= jacob H hr hw
 let u(x:G.Color):=Real.exp (-(κ/8)*‖x‖^2)
 let L:=estuary A κ; let K:=fiord A κ r
 let k:=κ/2*(2+D*r)*D; let a:= A.scale; have ha:0<a:= H.scale; have hk:0<k:=by unfold k; positivity; -- indentation
 let W(x:G.Color):= a* ((C+r⁻¹) * (‖x‖*u x) + k*(‖x‖^3*u x))
 have hL(x): 0 ≤ L x:= (mul_pos ha (Real.exp_pos _)).le
 have hg: Integrable L:= (gauss_owned G.Color (half_pos v)).const_mul a
 have hpW: Integrable W:=by
    have h₁:Integrable (fun x:G.Color=> ‖x‖ * u x):= by simpa only [pow_one] using (gauss_touch G.Color 1 (a:=κ/8) (by positivity))
    exact ((h₁.const_mul (C+r⁻¹)).add ( (gauss_touch G.Color 3 (a:=κ/8) (by positivity)).const_mul k)).const_mul a
 let t:=∫ x,W x
 have hv(x:G.Color):0 ≤ W x:=by unfold W u; positivity
 have ht:0≤t:=integral_nonneg hv
 have hx(x:G.Color): L x ≤ a*u x :=by
    apply mul_le_mul_of_nonneg_left _ ha.le; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (by linarith : -(κ/2)≤ -(κ/8)) (sq_nonneg _)
 refine ⟨t+1,by positivity,?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ)] with s g
 have hm(x:G.Color): |K s x-L x| ≤ s⁻¹* W x:=by
    let z:= ‖x‖; let y:= s⁻¹ • x; let q:= G.chord (G.lieExp y); have hy:s*‖y‖=‖x‖:=by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr g).le]; field_simp
    have hz:0≤z:=norm_nonneg _
    by_cases H': y ∈ closedBall 0 r
    · let v₁:=mouth G (κ*s^2) (G.lieExp y); let v₂:=Real.exp (-(κ/2)*z^2); have hf:L x=a*v₂:=rfl
      have H₃: ‖y‖≤r:= mem_closedBall_zero_iff.mp H'; have hj: K s x=(a*A.J y)*v₁:= indicator_of_mem H' _
      obtain ⟨_,_,h₂,h₃⟩:=U y H₃
      have hb:v₁=Real.exp (-(κ/2)*(s*q)^2):=by unfold v₁ mouth; congr 1; unfold q; rw [mul_pow,G.chord_price]; ring
      have he₁: v₁≤ u x:=by
        rw [hb]; apply Real.exp_monotone; have hc : ‖x‖ ≤ 2*(s*q):=by have hx: ‖y‖/2 ≤ q:=h₂; linarith only [hy,mul_le_mul_of_nonneg_left hx g.le]
        nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc 2) v.le]
      have he₂ : |v₁-v₂|≤ s⁻¹*(u x*(k*z^3)):=by rw [hb]; exact numeric_rim g (norm_nonneg _) hy H₃ hD.le v h₂ h₃
      have hv: |A.J y-1|≤C*(s⁻¹*z):= (hc _ H₃).trans_eq (by rw [show z=s*‖y‖ from hy.symm, inv_mul_cancel_left₀ g.ne'])
      rw [hj,hf,show a*A.J y*v₁-a*v₂=a*((A.J y -1)*v₁+(v₁-v₂)) by ring, abs_mul,abs_of_pos ha]; refine (mul_le_mul_of_nonneg_left (abs_add_le ..) ha.le).trans ?_; rw [abs_mul,abs_of_pos (mouth_pos _ _ _)]
      have h':0≤r⁻¹*(z*u x):=by unfold u; positivity
      exact (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul hv he₁ (mouth_pos _ _ _).le (by positivity)) he₂) ha.le).trans (by unfold W; change a*(C*(s⁻¹*z)*u x+s⁻¹*(u x*(k*z^3))) ≤ s⁻¹*(a*((C+r⁻¹)*(z*u x)+k*(z^3*u x))); linarith only [mul_nonneg (mul_nonneg (inv_nonneg.mpr g.le) ha.le) h'])
    · have h : K s x=0:= indicator_of_notMem H' _; rw [h,zero_sub,abs_neg,abs_of_nonneg (hL x)]; apply (hx x).trans; have hb:r≤‖y‖:= (lt_of_not_ge fun u=> H' (mem_closedBall_zero_iff.mpr u)).le
      have he:s*r≤z:= (mul_le_mul_of_nonneg_left hb g.le).trans_eq hy; have hz' : 0 ≤ u x:= (Real.exp_pos _).le; let U:=u x
      have hz'':s* (a*u x) ≤ a*(r⁻¹*(z*u x)):=by
         have hv:s≤r⁻¹*z:=by rw [mul_comm,←div_eq_mul_inv,le_div_iff₀ hr]; exact he
         linarith only [mul_le_mul_of_nonneg_right hv (mul_nonneg ha.le hz')]
      rw [mul_comm s⁻¹, ←div_eq_mul_inv,le_div_iff₀ g,mul_comm _ s]; apply hz''.trans; unfold W; change a* (r⁻¹*(z*u x))≤ a*((C+r⁻¹)*(z*u x) + k*(z^3*u x)); apply mul_le_mul_of_nonneg_left _ ha.le; rw [add_mul]; have hzₜ: 0≤C*(z*u x):=by positivity
      apply le_trans ?_ (le_add_of_nonneg_right (show 0≤k*(z^3*u x) by positivity)); linarith only [hzₜ]
 have hp: Measurable (K s):= by unfold K fiord; exact ((((measurable_const.mul H.borel : Measurable _).mul ((mouth_cont G _).measurable.comp G.lieExp_cont.measurable)).indicator isClosed_closedBall.measurableSet).comp (by fun_prop))
 have hb: Integrable (fun x=> K s x-L x):= (hpW.const_mul s⁻¹).mono' (hp.aestronglyMeasurable.sub hg.aestronglyMeasurable) (Eventually.of_forall hm) -- erroneous L meas
 have he:= (norm_integral_le_of_norm_le (hpW.const_mul s⁻¹) (Eventually.of_forall hm: ∀ᵐ x: G.Color, ‖K s x-L x‖ ≤ s⁻¹*W x)); have ht':Integrable (K s):=(hb.add hg).congr (Eventually.of_forall fun i=> sub_add_cancel _ _) -- tune
 rw [integral_const_mul,integral_sub ht' hg,show (∫ x,L x)=narrow A κ from ?_,Real.norm_eq_abs] at he
 · unfold K fiord at he; rw [Measure.integral_comp_inv_smul_of_nonneg volume (f:= (closedBall _ _).indicator _) g.le,smul_eq_mul,integral_indicator isClosed_closedBall.measurableSet,←kernel_integral A H hw _ (mouth_cont _ _).measurable] at he
   rw [Real.rpow_neg_one,mul_comm _ s⁻¹]; exact he.trans (mul_le_mul_of_nonneg_left (show t≤t+1 by linarith) (by positivity))
 unfold narrow L estuary; rw [integral_const_mul,GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
end YM.Sleigh
