import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import YM.Maxwell.PotentialKernel
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators
open GaussianFourier Maxwell
open scoped RealInnerProductSpace Topology
local notation "I"=> Complex.I
abbrev rider (x p:E4):ℂ:= Complex.exp (I*↑(inner ℝ x p))
abbrev veil (t:ℝ)(p:E4):ℝ:= Real.exp (-t*‖p‖^2)
abbrev Hη (t:ℝ)(p:E4):ℝ:=veil t p /(‖p‖^2)
variable {t:ℝ}
lemma unitR (x p:E4): ‖rider x p‖=1:=by unfold rider; rw [Complex.norm_exp]; simp
lemma borneR (z:ℝ)(w:0< z)(x:E4): let g:= fun p=> rider x p*(veil z p:ℂ); Integrable g volume ∧ ∫ p,g p=(Real.pi/(z:ℂ))^2*↑(Real.exp (-‖x‖^2/(4*z))):=by
 intro g; have he: g= fun p=> Complex.exp (-(z:ℂ) * (↑‖p‖:ℂ)^2+I*↑(inner ℝ x p)):=by
    funext p; simp [g,rider,veil,←Complex.exp_add,add_comm]
 rw [he]; have hz: 0<(z:ℂ).re:= w; refine ⟨integrable_cexp_neg_mul_sq_norm_add hz I x,(integral_cexp_neg_mul_sq_norm_add hz I x).trans ?_⟩
 rw [show Module.finrank ℝ E4=4 by simp]; norm_num [neg_div] -- tune
lemma puffer (t A:ℝ)(s:0<A): IntegrableOn (fun z:ℝ=> Real.exp (-z*A)) (Set.Ioi t) volume ∧ ∫ z in Set.Ioi t, Real.exp (-z*A) =Real.exp (-t*A)/A:=by
 let f(z:ℝ):= Real.exp (-z*A)
 let g(z:ℝ):= -(f z/A)
 have h(x:ℝ):HasDerivAt g (f x) x:=by
    refine HasDerivAt.congr_deriv ((((hasDerivAt_id' x).neg.mul_const A).exp.div_const A).neg) ?_; dsimp only [g,f,Pi.neg_apply]; field_simp
 have hp:Tendsto (fun x:ℝ=> -x*A) atTop atBot:=by
    apply Tendsto.congr ?_ ((tendsto_neg_atBot_iff.mpr (tendsto_id.atTop_mul_const s)) : Tendsto (fun x:ℝ=> -(x*A)) atTop atBot); intro i; ring
 have hx:Tendsto g atTop (𝓝 0):=by simpa only [neg_zero,zero_div] using (((show Tendsto f atTop (𝓝 0) from tendsto_exp_atBot.comp hp).div_const A).neg)
 have hk : IntegrableOn f (Set.Ioi t) volume:= integrableOn_Ioi_deriv_of_nonneg' (fun x _=>h x) (fun x _=>(Real.exp_pos _).le) hx
 refine ⟨hk, (integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _=> h x) hk hx).trans ?_⟩; unfold g f; ring
lemma heat_known (t:ℝ)(b:0<t): Integrable (veil t) volume ∧ ∫ p:E4, veil t p= (Real.pi/t)^2:=by
 have he(x:E4): ‖rider 0 x*(veil t x:ℂ)‖=veil t x:=by rw [norm_mul,unitR,one_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
 obtain ⟨h,u⟩:= borneR t b 0; refine ⟨(h.norm.congr (Eventually.of_forall he)),?_⟩
 have hv: rider (0:E4)=fun x=>1:=by ext x <;> simp [rider]
 change (∫ y:E4, rider 0 y*(veil t y:ℂ))=_ at u; simp_rw [show ∀ x:E4,rider (0:E4) x =1 from congrFun hv,one_mul] at u; rw [integral_complex_ofReal] at u; have hz:=u; simp at u; exact_mod_cast u
lemma Earnη (b:0<t): Integrable (fun p : ℝ × E4 => veil p.1 p.2) ((volume.restrict (Set.Ioi t)).prod volume):=by
 refine (integrable_prod_iff (by fun_prop)).mpr ⟨?_,?_⟩
 · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (v:t<x); exact (heat_known x (b.trans v)).1
 have hp: IntegrableOn (fun x:ℝ=> π^2*x^(- (2:ℝ))) (Set.Ioi t) volume:= (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2:ℝ)) < -1) b).const_mul _ -- check
 apply hp.congr; filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (v:t<x); have hv:= b.trans v; rw [show (∫ y:E4, ‖veil x y‖)=_ from (?_: (∫ y:E4, ‖veil x y‖)=(π/x)^2),Real.rpow_neg hv.le]; norm_num; ring
 rw [show (fun y:E4=>‖veil x y‖)=veil x from funext fun y=>Real.norm_of_nonneg (Real.exp_pos _).le]; exact (heat_known x hv).2
lemma cashH (p:E4)(h:p≠0) (t:ℝ): IntegrableOn (fun x:ℝ=>veil x p) (Set.Ioi t) volume ∧ ∫ x in Set.Ioi t, veil x p=Hη t p:=puffer _ _ (by have hx:=norm_pos_iff.mpr h; positivity)
lemma NZφ: ∀ᵐ p:E4,p≠0 := by rw [ae_iff]; rw [show {x:E4 | ¬x≠0}={0} from by ext; simp,measure_singleton]
lemma Hη_int (b:0<t):Integrable (Hη t) volume:=by
 have hv:Integrable (fun x:E4=>∫ y:ℝ in Set.Ioi t, ‖veil y x‖) volume:=((integrable_prod_iff' (Earnη b).aestronglyMeasurable).mp (Earnη b)).2
 apply hv.congr; filter_upwards [NZφ] with p h; rw [show (fun y:ℝ=> ‖veil y p‖)=(fun y=> veil y p) from funext fun y=>Real.norm_of_nonneg (Real.exp_pos _).le, (cashH p h t).2]
abbrev πnorm:ℝ:=((2*Real.pi)^4)⁻¹
abbrev TreeH (x: E4)(z:ℝ):ℝ:= (Real.pi/z)^2*Real.exp (-‖x‖^2/(4*z))
abbrev Woof (x:E4)(t:ℝ):= Green x* (1- Real.exp (-‖x‖^2/(4*t)))
lemma hedge (b:0<t)(x:E4): (∫ p:E4,rider x p*(Hη t p:ℂ))=(↑(∫ z:ℝ in Set.Ioi t,TreeH x z):ℂ):=by
 let S:= volume.restrict (Set.Ioi t); let f(z:ℝ)(p:E4):=rider x p*(veil z p:ℂ)
 have hf: Integrable (Function.uncurry f) (S.prod volume):=by
    apply (Earnη b).mono' (f:=Function.uncurry f) ?_ (Eventually.of_forall (fun y=>?_)) -- binder
    · unfold f; simp only [uncurry_def]; fun_prop
    simp only [uncurry,f,norm_mul,unitR x,one_mul,Complex.norm_real]; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
 rw [←integral_complex_ofReal]; calc
    (∫ p:E4,rider x p*(Hη t p:ℂ)) = ∫ p:E4,∫ z,f z p∂S:=by
       apply integral_congr_ae; filter_upwards [NZφ] with p h; unfold f; rw [integral_const_mul,integral_complex_ofReal,←(cashH p h t).2]
    _ = ∫ z,(∫ p:E4, f z p) ∂S:= (integral_integral_swap hf).symm -- tune
    _ = _:=by
       apply integral_congr_ae; filter_upwards [ae_restrict_mem measurableSet_Ioi] with z (h:t<z); rw [show (∫ p, f z p)=_ from (borneR z (b.trans h) x).2]; unfold TreeH; push_cast; rfl
lemma Woof_K (b:0<t)(x:E4)(q:x≠0): πnorm*(∫ z in Set.Ioi t, TreeH x z)=Woof x t:=by
 let A:= ‖x‖^2/4; let P:=π^2; have hp: 0<A:=by have he:=norm_pos_iff.mpr q; unfold A; positivity
 let f(z:ℝ):=Real.exp (-A/z)*P/A
 have he (z)(v:z∈ Set.Ici t):HasDerivAt f (TreeH x z) z:=by
    have hv:= b.trans_le v; unfold TreeH; rw [show -‖x‖^2/(4*z)= -A/z by unfold A; ring]; refine HasDerivAt.congr_deriv (((((hasDerivAt_const z (-A)).div (hasDerivAt_id' z) hv.ne').exp).mul_const P).div_const A) ?_; unfold P; simp only [Pi.div_apply]; field_simp; ring -- order
 have hh:Tendsto f atTop (𝓝 (P/A)):=by
    simpa only [f,Function.comp_apply,Real.exp_zero,one_mul] using ((((Real.continuous_exp.tendsto 0).comp (show Tendsto (fun z:ℝ=> -A/z) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_id)).mul_const P).div_const A)
 rw [integral_Ioi_of_hasDerivAt_of_nonneg' he (fun i _=>mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hh]; unfold f Woof; rw [show -‖x‖^2/(4*t)= -A/t by unfold A; ring]; unfold Green πnorm P normal A; field_simp <;> ring
end YM.StressFHeat
end
