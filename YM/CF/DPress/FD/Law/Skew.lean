import YM.CF.DPress.FD.Law.Dream
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Set Lattice MeasureTheory ProbabilityTheory Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {X Y Z I J:Type*}[MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z] [MeasurableSpace J] {μ:Measure X}{ν:Measure Y}{ξ:Measure Z}
namespace BasicIid
lemma skew [SFinite ν][SFinite ξ] (f:X→Y→Z)(h: Measurable (uncurry f))(p:∀ x, MeasurePreserving (f x) ν ξ): MeasurePreserving (fun c:X × Y=> (c.1,f c.1 c.2)) (μ.prod ν) (μ.prod ξ):=by
 let F (c:X × Y):=(c.1,f c.1 c.2); have ht:Measurable F:= measurable_fst.prodMk h; refine ⟨ht,Measure.ext fun S v => ?_⟩; rw [Measure.map_apply ht v,Measure.prod_apply (ht v),Measure.prod_apply v]; apply lintegral_congr; intro i; exact (p i).measure_preimage ((measurable_prodMk_left v).nullMeasurableSet)
lemma skew' [SFinite ν][SFinite ξ] (f:X→Y→Z)(G:X→Z→ J)(h: Measurable (uncurry f))(p:∀ x, MeasurePreserving (f x) ν ξ)(g:Measurable (uncurry G)) : (μ.prod ν).map (fun c:X ×Y=> G c.1 (f c.1 c.2)) = (μ.prod ξ).map (uncurry G):=by
 let H:=skew (μ:=μ) f h p; exact (Measure.map_map g H.measurable).symm.trans (by rw [H.map_eq])
lemma leaf [SFinite ξ][SFinite ν] (f:X→Y→ J)(G:X→Z→ J)(h:Measurable (uncurry f))(p:Measurable (uncurry G))(g:∀ x,ν.map (f x)=ξ.map (G x)) : (μ.prod ν).map (uncurry f)=(μ.prod ξ).map (uncurry G):=by
 apply Measure.ext; intro S v; rw [Measure.map_apply h v,Measure.map_apply p v,Measure.prod_apply (h v),Measure.prod_apply (p v)]; refine lintegral_congr fun x=> ?_; change ν ((f x) ⁻¹' S) = ξ ((G x) ⁻¹' S); rw [←Measure.map_apply (show Measurable (f x) from h.comp measurable_prodMk_left) v, g,Measure.map_apply (show Measurable (G x) from p.comp measurable_prodMk_left) v]
-- shuffle triple for tag. perhaps use actual sampler: independent Stage × Sip arrays then G product, separately use $β$ mapping.Other.Dep supply. 
end BasicIid
end YM.CF.DPress.FD
