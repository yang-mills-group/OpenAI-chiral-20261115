import YM.SU5.Reconstruction.Quartz.Tunnel
import Mathlib.Analysis.Complex.PhragmenLindelof
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Ravin
open Function Set Filter MeasureTheory Metric Topology Complex
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace Classical Interval
abbrev κ := Quarterπ
lemma potential :0<(κ:ℝ):= half_pos Real.pi_pos
lemma paid : (κ:ℝ)≤2:= by unfold κ Quarterπ; linarith[Real.pi_le_four] -- namespace
noncomputable def dome(a b:ℝ):Set ℂ:= Icc a b ×ℂ Icc 0 κ
noncomputable def spin(a b:ℝ):Set ℂ:= Ioo a b ×ℂ Ioo 0 κ
abbrev D:= dome (-3) 3
abbrev Dw:= spin (-3) 3
abbrev sightParam(n:ℕ):ℝ:=n+1
structure Studies (F:ℕ→ℂ→ℂ)(M C:ℝ):Prop where
 C0 : 1≤C
 M0 : 0≤M
 reads (n):ContinuousOn (F n) D
 polish(n):DifferentiableOn ℂ (F n) Dw
 landscape(n)(p:ℂ)(q:p∈D):‖F n p‖≤M*Real.exp (sightParam n*C*p.im) -- growth maybe n+1
 capitates(n)(p:ℂ)(q:p∈D)(e:p.im=κ): ‖F n p‖≤ M*Real.exp (-sightParam n * (6*C))
variable {F:ℕ→ℂ→ℂ}{M C:ℝ}(s:Studies F M C)
noncomputable def harp (C:ℝ)(z:ℂ):ℝ:=z.im*(-1+C*z.re^2-C*z.im^2/3)
noncomputable def land (C:ℝ)(z:ℂ):ℂ:= I*(z-C*z^3/3)
lemma land_re(C:ℝ)(z:ℂ) : (land C z).re=harp C z := by unfold land harp; rw[pow_succ]; simp[mul_re,mul_im,pow_two]; ring -- neg? I*(z-C*..)= -y+. yes
include s
lemma lantern (n:ℕ)(z:ℂ)(h:z∈D): ‖F n z‖≤M*Real.exp (sightParam n * harp C z):= by
 let N:=sightParam n; have he:0 ≤ N:=by unfold N sightParam; positivity
 let f(z:ℂ):= F n z*Complex.exp (-N*land C z); -- coercion
 have hx(z:ℂ): ‖f z‖≤ M ↔ ‖F n z‖≤ M*Real.exp (sightParam n*harp C z):= by unfold f; rw[norm_mul,norm_exp]; unfold N; simp only [mul_re,ofReal_im,ofReal_re,neg_re,land_re, zero_mul,sub_zero,neg_mul,Real.exp_neg]; rw[← div_eq_mul_inv]; exact div_le_iff₀ (Real.exp_pos _)
 have hr : closure Dw=D:=by rw [Dw, D, dome,spin,closure_reProdIm,closure_Ioo potential.ne,closure_Ioo (by norm_num : (-3:ℝ)≠3)]
 have hb : DiffContOnCl ℂ f Dw:= by
    let g(z:ℂ):= cexp (-↑N*land C z); have p:Differentiable ℂ g:= by unfold g land;fun_prop
    exact ⟨(s.polish n).mul p.differentiableOn,(show ContinuousOn (F n) (closure Dw) from hr.symm ▸ (s.reads n)).mul p.continuous.continuousOn⟩
 apply (hx z).1; apply norm_le_of_forall_mem_frontier_norm_le ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _)) hb _ (hr ▸ h)
 intro w p; have hp:w∈D:= hr ▸ frontier_subset_closure p; have k: C≥1:=s.C0; have v:0<C:=by linarith
 obtain ⟨a,b⟩:= (show w.im∈ Icc (0:ℝ) κ from hp.2); let d:=w.im; let d':=w.re
 have hd:d≤2:=le_trans b paid; have ht: d*d≤2*2:= mul_le_mul hd hd a (by norm_num)
 by_cases r: w.im=κ
 · apply (hx w).2; apply (s.capitates n w hp r).trans; unfold harp; refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) s.M0
   change -N*(6*C)≤ N*(d*(-1+C*d'^2-C*d^2/3)); rw [neg_mul,←mul_neg]; gcongr N * ?_; -- LHS 6*C ≥ d(1+ Cd²/3); for d=2 ->2+8C/3; ok
   nlinarith [ show d=d from rfl, show 0≤d from a, mul_nonneg a (sq_nonneg d), mul_nonneg (show 0≤d from a) (mul_nonneg v.le (sq_nonneg d')),mul_le_mul_of_nonneg_left ht (mul_nonneg v.le (show 0≤d from a)),mul_le_mul_of_nonneg_left hd v.le]
 apply (hx w).2; apply (s.landscape n w hp).trans; unfold harp; refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) s.M0
 change N*C*d≤N*(d*(-1+C*d'^2-C*d^2/3)); by_cases i:w.im=0; · simp[d,i]
 rw [frontier_reProdIm,frontier_Ioo potential,closure_Ioo potential.ne,frontier_Ioo (by norm_num : (-3:ℝ)<3), closure_Ioo (by norm_num :(-3:ℝ)≠3)] at p
 have t:d'^2=9:=by
   have ht:= p.resolve_left (fun v=>(show False from ((show w.im=0∨w.im=κ from v.2).elim i r))); unfold d'; rcases (show w.re=(-3:ℝ)∨w.re=3 from ht.1) with h|h <;> rw [h] <;> norm_num
 rw [t,mul_assoc N,mul_comm C d]; gcongr; nlinarith [mul_le_mul_of_nonneg_left ht v.le] -- tune
lemma slide (x:ℝ)(p:x∈ Icc (-(1/(4*C))) (1/(4*C))) : x∈ Icc (-3:ℝ) 3:= by
 have v:= s.C0; have h:1/(4*C)≤(1:ℝ):= (div_le_one (by linarith)).2 (by linarith); constructor<;> linarith [p.1,p.2]
lemma subsidence (z:ℂ)(k:z∈dome (-(1/(4*C))) (1/(4*C)))(n:ℕ) : ‖F n z‖ ≤ M * Real.exp (-sightParam n * (z.im/2)):= by
 obtain ⟨p,q⟩:=k; apply (lantern s n z ⟨slide s z.re p,q⟩).trans; have hc:=s.C0; have ha:0≤sightParam n:=by unfold sightParam; positivity;
 have hm:0≤ z.im:=q.1; refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) s.M0
 rw [neg_mul,← mul_neg]; gcongr sightParam n * ?_; unfold harp; rw [show -(z.im/2)=z.im*(-1/2) from by ring]; gcongr z.im * ?_ -- grows
 have hx : |z.re|≤1/(4*C):= abs_le.mpr p; have h: 0<C:=by linarith
 have hv : |z.re| ≤1:= hx.trans ((div_le_one (by positivity)).2 (by linarith)); nlinarith [(le_div_iff₀ (show 0<4*C by positivity)).mp hx,abs_mul_abs_self z.re,mul_self_le_mul_self (abs_nonneg z.re) hv, mul_le_mul_of_nonneg_left hv (mul_nonneg h.le (abs_nonneg z.re)), mul_nonneg h.le (sq_nonneg z.im)]
lemma decreases (z:ℂ)(k:z∈dome (-(1/(4*C))) (1/(4*C)))(e:0<z.im): Tendsto (fun i=> F i z) atTop (𝓝 0) := by
 refine squeeze_zero_norm' (Eventually.of_forall (subsidence s z k)) ?_
 simp_rw [neg_mul, ←mul_neg,mul_comm (sightParam _)]
 let k:= tendsto_atTop_add_const_right _ (1:ℝ) tendsto_natCast_atTop_atTop -- tune syntax
 have hv : Tendsto (fun n:ℕ=> -(z.im/2) * (sightParam n)) atTop atBot:= k.const_mul_atTop_of_neg (neg_lt_zero.mpr (half_pos e)); simpa using (Real.tendsto_exp_atBot.comp hv).const_mul M
end YM.Quartz.Ravin
