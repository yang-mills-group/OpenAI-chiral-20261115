import GaugeFieldConstruction.Zlode
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators
open GaussianFourier Maxwell Analysis
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
-- random packet billing. limit poly through2, compact. arbitrary sites
structure HopeC (X:Type*) [TopologicalSpace X][MeasurableSpace X] where
 μ:Measure X
 [isProb: IsProbabilityMeasure μ]
 site:Set X
 k: IsCompact site
 onA:∀ᵐ x ∂μ,x∈site
attribute [instance] HopeC.isProb
variable {X Y V:Type*}[TopologicalSpace X][MeasurableSpace X][TopologicalSpace Y][MeasurableSpace Y]
lemma span_v [T2Space X][BorelSpace X] [NormedAddCommGroup V](N:HopeC X)(f:X→V)(v: ContinuousOn f N.site): Integrable f N.μ:=by
 have hf: IntegrableOn f N.site N.μ:= v.integrableOn_compact N.k; rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem N.onA] at hf
lemma span_c [T2Space X][BorelSpace X][NormedAddCommGroup V](N:HopeC X) {f:X→V}(v:Continuous f):Integrable f N.μ:=span_v N _ v.continuousOn
namespace HopeC
def lift [BorelSpace X][BorelSpace Y][T2Space Y](H:HopeC X) (f:X→Y)(p: Continuous f): HopeC Y where
 μ:= H.μ.map f
 isProb:= Measure.isProbabilityMeasure_map (p.aemeasurable)
 site:=f '' H.site
 k:=H.k.image p
 onA:= (ae_map_iff p.aemeasurable ((H.k.image p).measurableSet)).mpr (H.onA.mono fun i h=>Set.mem_image_of_mem _ h)
lemma rolled [BorelSpace X][BorelSpace Y][T2Space Y][NormedAddCommGroup V][NormedSpace ℝ V](H:HopeC X)(f:X→Y)(p:Continuous f)(g:Y→V)(v:ContinuousOn g (f '' H.site)) : (∫ y,g y∂(lift H f p).μ)=∫ x,g (f x) ∂H.μ:= by apply integral_map p.aemeasurable; exact (span_v (lift H f p) _ v).aestronglyMeasurable
def pairs (H:HopeC X)(G:HopeC Y) : HopeC (X×Y) where
 μ:= H.μ.prod G.μ
 site:= H.site ×ˢ G.site
 k:=H.k.prod G.k
 onA:=by filter_upwards [Measure.quasiMeasurePreserving_fst.ae H.onA,Measure.quasiMeasurePreserving_snd.ae G.onA] with x v h; exact ⟨v,h⟩
end HopeC
variable (H:HopeC E4)
abbrev ξH (p:E4):ℂ:=∫ x, rider x p∂H.μ
lemma concert (p:E4): Integrable (fun x=> rider x p) H.μ :=span_c H (by unfold rider; fun_prop)
lemma sum_r (x y p:E4):rider (x+y) p=rider x p*rider y p:=by unfold rider; rw [inner_add_left,Complex.ofReal_add,mul_add,Complex.exp_add]
lemma opp_r (x p:E4):rider (-x) p=star (rider x p):=by unfold rider; rw [inner_neg_left,Complex.ofReal_neg,Complex.star_def, ←Complex.exp_conj,map_mul,Complex.conj_I]; simp
namespace HopeC
variable (G:HopeC E4)
def addQ := lift (pairs H G) (fun p=> p.1+p.2) (by fun_prop)
lemma adds (p:E4): ξH (addQ H G) p= ξH H p* ξH G p:=by unfold addQ ξH; rw [rolled (v:=(show Continuous (fun x=> rider x p) from by unfold rider; fun_prop).continuousOn)]; simp_rw [sum_r]; exact integral_prod_mul (μ:=H.μ) (ν:=G.μ) (fun x=>rider x p) (fun y=>rider y p)
def rev := lift H (fun x=>-x) (by fun_prop)
lemma revs(p:E4): ξH (rev H) p=star (ξH H p):=by unfold rev ξH; rw [rolled (v:=(show Continuous (fun x=>rider x p) from by unfold rider; fun_prop).continuousOn)]; simp_rw [opp_r]; exact integral_conj (f:=fun x=> rider x p)
lemma add_l [NormedAddCommGroup V][NormedSpace ℝ V][SecondCountableTopology V](p:E4→V)(h:ContinuousOn p (addQ H G).site) : (∫ z,p z∂(addQ H G).μ)=∫ x,(∫ y,p (x+y)∂G.μ)∂H.μ:=by
 unfold addQ; rw [rolled (v:=h)]; apply integral_prod; exact span_v (pairs H G) _ (h.comp (by apply Continuous.continuousOn; fun_prop) fun i p=> Set.mem_image_of_mem _ p)
def point (x:E4): HopeC E4 where
 μ:=Measure.dirac x
 site:={x}
 k:=isCompact_singleton
 onA:=by simp
lemma xi_point(x p:E4): ξH (point x) p=rider x p:= integral_dirac ..
end HopeC
variable (w:List Axis)(h:w.length≤2)
include h
lemma Hanse (t:ℝ)(b:0<t): Integrable (fun p=> ξH H p * kip w t p) volume ∧ (πnorm:ℂ)*(∫ p, ξH H p * kip w t p)= ∫ x, retK w t x∂H.μ:=by
 let f(p x:E4):= rider x p*kip w t p; have hp:Integrable (Function.uncurry f) (volume.prod H.μ):=by
    refine (integrable_prod_iff ?_).mpr ⟨Eventually.of_forall (fun x=>(concert H x).mul_const (kip w t x)),?_⟩
    · unfold uncurry f; exact (show Continuous fun p:E4 × E4=> rider p.2 p.1 from by unfold rider; fun_prop).aestronglyMeasurable.mul (kip_int _ t b h|>.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst) -- underscore ambiguity
    refine (kip_int w t b h).norm.congr (Eventually.of_forall fun i=>?_); unfold f; simp only [Function.uncurry_apply_pair,norm_mul,unitR,one_mul,integral_const, measureReal_univ_eq_one,one_smul]
 have he:(fun p=>ξH H p*kip w t p)= (fun p=> ∫ x,f p x∂H.μ):=funext fun p=>by unfold ξH f; rw [integral_mul_const]
 rw [he]; constructor
 · exact hp.integral_prod_left -- orientation tune
 rw [integral_integral_swap hp,← integral_const_mul] <;> rfl
lemma approach (p:0∉H.site) : Tendsto (fun z:ℝ=> (πnorm:ℂ)*(∫ y,ξH H y * kip w z⁻¹ y)) atTop (𝓝 (∫ y, (↑(regD w Green y):ℂ)∂H.μ)):=by
 let f (x:E4):ℂ:= ↑(regD w Green x); let g(z:ℝ)(x:E4):ℂ:= (regD w (fun x=>Woof x z⁻¹) x)
 obtain ⟨V,L,U⟩:= autumnP w H.site H.k p; have hp: Integrable f H.μ:=span_v H _ (fun x h=>(Complex.continuous_ofReal.continuousAt.comp ((quietC w _ _ (freeSmooth (fun e=> p (e▸h)))).continuousAt)).continuousWithinAt)
 have hh(i:ℝ):Integrable (g i) H.μ:=span_v H _ (fun x h=>(Complex.continuous_ofReal.continuousAt.comp ((quietC w _ _ (Woof_M _ _ fun e=> p (e▸h))).continuousAt)).continuousWithinAt)
 have hx: Tendsto (fun z:ℝ=>∫ x,g z x∂H.μ) atTop (𝓝 (∫ x,f x∂H.μ)):= by
    rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ L
    filter_upwards [U] with i u; rw [← integral_sub (hh i) hp]; apply (norm_integral_le_of_norm_le (integrable_const (V i)) (H.onA.mono fun x h=>?_)).trans; · simp
    convert u x h using 1; simp only [g,f, ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
 apply hx.congr'; filter_upwards [eventually_gt_atTop (0:ℝ)] with i e; rw [(Hanse H w h i⁻¹ (inv_pos.mpr e)).2]; exact integral_congr_ae (H.onA.mono fun y v=> (cell_K _ _ h (inv_pos.mpr e) _ (fun k=>p (k▸v))).symm)
end YM.StressFHeat
end
