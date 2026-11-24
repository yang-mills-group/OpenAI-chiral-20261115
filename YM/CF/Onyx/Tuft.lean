import YM.CF.Onyx.Hail
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory
open YM.Stationary (Gaia cartWeight springAx spring_unit springTouch)
variable {u:ℝ}{x:Gaia}
def elf(x:Gaia)(u:ℝ):= Real.exp (-fieldV x/u)
def gale(x:Gaia)(u:ℝ):= Real.pi^2/fieldV x*(1-elf x u)
def purr(u:ℝ)(x p:Gaia):=burn x p*(pet u p:ℂ)
lemma fen(h:x≠0):0<fieldV x:=by unfold fieldV; positivity
lemma nap (U:ℝ)(e:0<U): Tendsto (fun y:ℝ=> Real.exp (-U/y)) atTop (𝓝 1):=by
 have he:= Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_inv_atTop_zero (𝕜:=ℝ)).const_mul (-U)); simpa only [Function.comp_def,mul_zero, Real.exp_zero, ←div_eq_mul_inv] using he
lemma aery (h:x≠0)(p:0<u): (∫ v:Gaia, purr u x v)=(gale x u:ℂ):=by
 have ht:= headR x p; have hx:(fun v:Gaia=>∫ w in Set.Ioi u,rafter x (w,v))=ᵐ[volume](purr u x):=(show ∀ᵐ v:Gaia, v≠0 by rw [ae_iff]; simp).mono fun i e=>roof _ _ e _
 rw [← integral_congr_ae hx, ← integral_prod_symm _ ht,integral_prod _ ht]; rw [setIntegral_congr_fun (s:=Set.Ioi u) (g:=fun w=> (((Real.pi/w)^2 * elf x w :ℝ):ℂ)) measurableSet_Ioi (fun i e=>(fare x (p.trans e)).2),integral_complex_ofReal]; congr 1
 let G(w):= -(gale x w); let K:=fieldV x; have he:0<K:=fen h
 have hv:Tendsto G atTop (𝓝 0):=by
    have hh:= nap K he; have ht:= Tendsto.const_sub 1 hh; simpa [G,gale,elf] using (ht.const_mul (Real.pi^2/K)).neg
 rw [integral_Ioi_of_hasDerivAt_of_nonneg' (g':=fun w=>(Real.pi/w)^2*elf x w) _ (fun i _=>mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hv]; · simp [G]
 intro r w; have hx:=p.trans_le w; have hg:= (((((hasDerivAt_const r (-fieldV x)).div (hasDerivAt_id' r) hx.ne').exp).const_sub 1).const_mul (Real.pi^2 /fieldV x)).neg; -- sign
 unfold G gale elf; convert hg using 1 <;> try rfl
 simp only [Pi.div_apply,mul_neg,zero_mul,mul_one]; have hx:=fen h; field_simp <;> ring
lemma siren (h:0<u)(x:Gaia): Integrable (purr u x) :=by
 refine (pen h).1.mono' ?_ (ae_of_all _ fun i=> ?_); unfold purr pet tog burn; apply Measurable.aestronglyMeasurable; fun_prop
 unfold purr; rw [norm_mul,iron,one_mul,Complex.norm_real,Real.norm_of_nonneg (by unfold pet tog; positivity)]
def nerve (a:Axis)(u:ℝ)(x p:Gaia):=Complex.I*(p a:ℂ)*purr u x p
def dye(u:ℝ)(x:Gaia):= Real.pi^2/(fieldV x)^2 * (elf x u*(1+fieldV x/u)-1)
def errH (a:Axis)(x:Gaia)(r:ℝ):=x+r • springAx a
lemma sed(p:Gaia)(a:Axis): |p a|≤‖p‖:=by rw [← springTouch a,abs_le]; have ht:= norm_inner_le_norm (𝕜:=ℝ) (springAx a) p; rw [spring_unit,one_mul] at ht; exact abs_le.mp ht
lemma rite (r u:ℝ)(x p:Gaia)(a:Axis): HasDerivAt (fun z=> purr u (errH a x z) p) (nerve a u (errH a x r) p) r:=by
 have hh(z):inner ℝ (errH a x z) p=inner ℝ x p+z*p a:=by rw [errH,inner_add_left,real_inner_smul_left,springTouch]
 unfold nerve purr burn; simp_rw [hh]; -- lift derivative
 have ht:= ((hasDerivAt_id' r).mul_const (p a)).const_add (inner ℝ x p); have hv:= (((ht.ofReal_comp).const_mul Complex.I).cexp).mul_const (pet u p:ℂ); -- tune
 convert hv using 1 <;> try rfl
 rw [one_mul]; ring
lemma dial (a:Axis)(u:ℝ)(x p: Gaia): ‖nerve a u x p‖≤ house u p:=by
 unfold nerve house purr; rw [norm_mul,norm_mul,norm_mul,iron,one_mul,Complex.norm_I, one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real]; by_cases h:p=0
 · subst p; simp [pet]
 have hh :0<‖p‖:=norm_pos_iff.mpr h; have hl:0≤pet u p:=div_nonneg (Real.exp_pos _).le (sq_nonneg _); rw [Real.norm_of_nonneg hl]; exact (mul_le_mul_of_nonneg_right (sed ..) hl).trans_eq (by unfold pet; field_simp)
lemma reek(h:0<u)(a:Axis)(x:Gaia):Integrable (nerve a u x):=by
 refine (pen h).2.mono' ?_ (Eventually.of_forall fun i=>dial ..); unfold nerve purr burn pet tog; apply Measurable.aestronglyMeasurable; fun_prop
lemma quake_v (h:0<u)(x:Gaia)(a:Axis): HasDerivAt (fun z:ℝ=>∫ p, purr u (errH a x z) p) (∫ p,nerve a u (errH a x 0) p) 0:=by
 let F(t:ℝ):=purr u (errH a x t); let V(t:ℝ):=nerve a u (errH a x t)
 exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=V) (univ_mem (f:=𝓝 0)) (Eventually.of_forall fun i=> (siren h _).aestronglyMeasurable) (siren h _) (reek h a _).aestronglyMeasurable (Eventually.of_forall fun x y _=>dial ..) (pen h).2 (Eventually.of_forall fun x r _=>rite ..)).2 -- defeq
lemma spring_v(a:Axis)(x:Gaia) : HasDerivAt (fun z:ℝ=>fieldV (errH a x z)) (x a/2) 0:=by
 let T(t:ℝ):= x+t • springAx a; have he:= ((hasDerivAt_id' (0:ℝ)).smul_const (springAx a)).const_add x; rw [one_smul] at he;
 have hg:= he.inner ℝ he; unfold errH fieldV; simp_rw [← real_inner_self_eq_norm_sq]; have hv:=hg.div_const 4; rw [show ((inner ℝ (x+ (0:ℝ) • springAx a) (springAx a))+inner ℝ (springAx a) (x+(0:ℝ) • springAx a))/4=x a/2 from (by rw [zero_smul,add_zero,real_inner_comm (springAx a) x, springTouch]; ring)] at hv; exact hv
lemma cue(a:Axis)(p:0<u)(h:x≠0): HasDerivAt (fun z:ℝ=> gale (errH a x z) u) (dye u x*(x a/2)) 0:=by
 let F:=fieldV x; have hx:= fen h; have he:errH a x 0=x:=by simp [errH]
 have ht:=spring_v a x; have hz:= (((hasDerivAt_const _ (Real.pi^2)).div ht (by rw [he]; exact hx.ne')).mul (((ht.neg.div_const u).exp).const_sub 1))
 unfold gale elf; convert hz using 1 <;> try rfl
 simp only [he,Pi.neg_apply,Pi.div_apply]; unfold dye elf; field_simp; ring
lemma say(a:Axis)(p:0<u)(h:x≠0): (∫ v,nerve a u x v)= ((dye u x*(x a/2):ℝ):ℂ):=by
 let F:=errH a x; have he:errH a x 0=x:=(by simp [errH]); have hv:=cue a p h |>.ofReal_comp
 have ht:= quake_v p x a; rw [he] at ht; refine HasDerivAt.unique ht (hv.congr_of_eventuallyEq ?_); filter_upwards [(show Continuous F by unfold F errH; fun_prop).continuousAt.eventually_ne (by change F 0≠_; change errH a x 0≠_; rwa [he])] with i hi; exact aery hi p -- tune
end YM.CF.Onyx
