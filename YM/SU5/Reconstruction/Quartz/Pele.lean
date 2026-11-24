import YM.SU5.Reconstruction.Quartz.HillGlass
import YM.SU5.Reconstruction.Sleet.Shelter
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace
open Ravin
abbrev Du:= ℝ × ℝ
abbrev Ba:= ℂ × ℂ
noncomputable def swap (s:ℝ) : Du→ₗ[ℝ] Du:= LinearMap.prodMap (Real.exp (-s) • (1: ℝ→ₗ[ℝ]ℝ)) (Real.exp s • (1:ℝ→ₗ[ℝ]ℝ))
-- transform from local coords at seam into global observer orientation (common-sign adjustment)
lemma at_swap(s:ℝ)(x:Du):swap s x= (Real.exp (-s) * x.1, Real.exp s * x.2):= rfl
lemma swap_trans (s:ℝ)(x:Du): swap (-s) (swap s x) = x:= by simp [at_swap,Real.exp_neg]
lemma swap_rest (s:ℝ)(x:Du): swap s (swap (-s) x)= x:=by simpa using swap_trans (-s) x
@[fun_prop] lemma swap_cont(s:ℝ): Continuous (swap s) := (swap s).continuous_of_finiteDimensional
lemma measure_swap (s:ℝ) : MeasurePreserving (swap s) := by -- args volumes implicit default?' 
 refine ⟨(swap_cont s).measurable,?_⟩
 have h: LinearMap.det (swap s)=1:= by unfold swap; rw [LinearMap.det_prodMap]; simp [← Real.exp_add]
 rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by simp [h]),h]; simp
noncomputable def hike (s:ℝ):Du→Du:=fun x=> swap s (x.1+x.2,x.2)
@[fun_prop] lemma hike_cont (s:ℝ):Continuous (hike s):=by unfold hike; fun_prop
noncomputable def stroll(s:ℝ): Du ≃ₜ Du where
 toFun:=hike s
 invFun x:=((swap (-s) x).1-(swap (-s) x).2,(swap (-s) x).2)
 left_inv x:= by dsimp only [hike]; simp only [swap_trans]; simp
 right_inv x:=by simp [hike,swap_rest]
 continuous_toFun:=hike_cont s
 continuous_invFun:=by fun_prop
lemma hike_pays(s:ℝ):MeasurePreserving (hike s) volume volume:= (measure_swap s).comp (measurePreserving_add_prod volume volume)
lemma hike_integral (s:ℝ){V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V] (f:Du→V): (∫ x:Du,f (hike s x))=∫ x:Du,f x:=(hike_pays s).integral_comp (stroll s).measurableEmbedding f
lemma hike_integrable (s:ℝ){V:Type*}[NormedAddCommGroup V](f:Du→V): Integrable (f ∘ hike s) ↔ Integrable f:= (hike_pays s).integrable_comp_emb (stroll s).measurableEmbedding
noncomputable def pressure (t:Du):ℝ:= t.1^2+t.2^2
noncomputable def wallRate(b:ℝ)(t:Du):ℝ:= b*Real.exp (-b*pressure t)
lemma rate_pos(b:ℝ)(t:Du)(p:0<b):0<wallRate b t:= by unfold wallRate; positivity
lemma fullWarm (b:ℝ)(p:0<b) : Integrable (wallRate b):= by
 let f(x:ℝ):= Real.exp (-b*x^2); have h:Integrable f:=integrable_exp_neg_mul_sq p
 unfold wallRate pressure; simp_rw [ mul_add, Real.exp_add]; exact (h.mul_prod h).const_mul _
lemma costs (b:ℝ)(p:0<b) : (∫ x:Du, wallRate b x)= Real.pi:=by
 simp_rw [wallRate,pressure,mul_add,Real.exp_add]; rw [integral_const_mul]; change b*(∫ x:Du, _ ∂(volume.prod volume))=_
 rw [integral_prod_mul (fun x:ℝ=> Real.exp (-b*x^2)) (fun x:ℝ=> Real.exp (-b*x^2)),integral_gaussian,← pow_two,Real.sq_sqrt (by positivity:0≤Real.pi/b)]; field_simp
open Complex
noncomputable def Largo (t:Du):Ba:= ((t.1:ℂ),(t.2:ℂ))
noncomputable def Forge (v:Ba) : Du:= (v.1.re,v.2.re)
noncomputable def Eddy (v:Ba) : Du:= (v.1.im,v.2.im)
noncomputable def Blaze (b:ℝ)(v:Ba):ℂ := (b:ℂ)*Complex.exp (-(b:ℂ)*(v.1^2+v.2^2))
lemma blaze_land(b:ℝ)(t:Du):Blaze b (Largo t)=(wallRate b t:ℂ):=by unfold Blaze Largo wallRate pressure; push_cast; rfl
lemma shines (z:ℂ): (z^2).re= z.re^2-z.im^2:=by simp only [pow_two, Complex.mul_re]
lemma blaze_fire(b:ℝ)(w:Ba)(p:0≤b): ‖Blaze b w‖= wallRate b (Forge w)*Real.exp (b*pressure (Eddy w)):=by
 unfold Blaze wallRate pressure Forge Eddy; rw [norm_mul,norm_exp,Complex.norm_real,Real.norm_of_nonneg p,mul_assoc,←Real.exp_add]; simp only[neg_im, ofReal_re,ofReal_im, add_re, shines,mul_re,neg_re,neg_zero,zero_mul,sub_zero]; congr 2; ring
lemma toll {b:ℝ}(p:0<b)(w:Ba)(v:Du): ‖Blaze b (Largo v-w)‖= wallRate b (v-Forge w)*Real.exp (b*pressure (Eddy w)):=by
 rw [blaze_fire _ _ p.le, show Forge (Largo v-w)= v-Forge w from rfl]; simp [pressure,Eddy,Largo] -- rfl?
lemma forge_add (A:ℝ)(a v:Du)(p:0<A): ‖Blaze A (Largo v-Largo a)‖=wallRate A (v-a):=by
 rw [show Largo v-Largo a= Largo (v-a) from (by ext1 <;> simp [Largo]),blaze_land,Complex.norm_real,Real.norm_of_nonneg (rate_pos _ _ p).le]
noncomputable def vat (b:ℝ)(w:Ba)(f:Du→ℂ):ℂ:=∫ x:Du,Blaze b (Largo x-w)* f x
-- resources on the whole weighted cylinder
lemma pond (b:ℝ)(w:Du)(p:0<b) : Integrable (fun x:Du=>wallRate b (x-w)) volume := (measurePreserving_add_right volume (-w)).integrable_comp_emb (Homeomorph.addRight (-w)).measurableEmbedding |>.2 (fullWarm b p) -- tune sub align
lemma vat_cask (b:ℝ)(w:Du) (p:0<b): (∫ x:Du,wallRate b (x-w))= Real.pi:= by rw[← costs b p]; simp_rw [sub_eq_add_neg]; rw[integral_add_right_eq_self _ (-w)] -- tune
lemma vat_score (b:ℝ)(w:Ba)(p:0<b)(f:Du→ℂ) (B:ℝ)(_q:0 ≤ B)(m:AEStronglyMeasurable f volume)(e:∀ t,‖f t‖≤B): Integrable (fun x:Du=>Blaze b (Largo x-w)* f x) ∧ ‖vat b w f‖≤(Real.pi*B)*Real.exp (b*pressure (Eddy w)):= by
 let c:=Real.exp (b*pressure (Eddy w)); have hc:0≤c:=(Real.exp_pos _).le; let g(u:Du):= wallRate b (u-Forge w)*(c*B); have h(x:Du): ‖Blaze b (Largo x-w)*f x‖≤ g x:=by rw[norm_mul]; refine (mul_le_mul_of_nonneg_left (e x) (norm_nonneg _)).trans_eq ?_; rw[toll p,mul_assoc]
 let Y(x):=Blaze b (Largo x-w)* f x; have s:Integrable g volume:=(pond b _ p).mul_const (c*B); have v:Integrable Y volume:= s.mono' ((show Continuous (fun x:Du=> Blaze b (Largo x-w)) from (by unfold Blaze Largo; fun_prop)).aestronglyMeasurable.mul m) (ae_of_all _ h)
 refine ⟨v,(norm_integral_le_integral_norm Y).trans ((integral_mono v.norm s h).trans_eq ?_)⟩
 unfold g c; rw[integral_mul_const, vat_cask b _ p]; ring
end YM.Quartz.Waltz
