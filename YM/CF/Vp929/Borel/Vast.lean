import Mathlib.Probability.Kernel.Representation
import YM.CF.Vp929.Borel.Measure
set_option autoImplicit false
set_option maxHeartbeats 760000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Set Function MeasureTheory ProbabilityTheory unitInterval
open scoped Classical Topology ENNReal NNReal
private theorem hMap (μ:Measure ℝ)[IsProbabilityMeasure μ][NullSingletonClass μ] :∃ g:ℝ→I,MeasurePreserving g μ volume:=by
 let g:=cdf μ; let v(x:ℝ):I:= ⟨g x, cdf_nonneg _ _,cdf_le_one _ _⟩; have hc:Continuous g:=by
   apply continuous_iff_continuousAt.mpr; intro x; have he:Function.leftLim g x=g x:= le_antisymm (g.mono.leftLim_le le_rfl) (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp ((g.measure_singleton x).symm.trans (by rw [show g.measure=μ from measure_cdf μ]; apply measure_singleton))))
   exact continuousAt_iff_continuous_left'_right'.mpr ⟨(g.mono.continuousWithinAt_Iio_iff_leftLim_eq).mpr he,(g.right_continuous x).mono Ioi_subset_Ici_self⟩
 have t:Measurable v:=(hc.subtype_mk (fun x=> (v x).property)).measurable; let m:=μ.map v; haveI:IsProbabilityMeasure m:= Measure.isProbabilityMeasure_map (t.aemeasurable); refine ⟨v,t, Measure.ext_of_Iic m volume ?_⟩; intro x
 have hx(a:ℝ)(ha:0<a)(hb:a<1):∃ b:ℝ,g b=a:=by
    obtain ⟨x,hx⟩:= ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds ha)).exists; obtain ⟨y,hy⟩:= ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hb)).exists; exact intermediate_value_univ x y hc ⟨(hx: g x<a).le,(hy:a<g y).le⟩
 rw [volume_Iic]; rw [← ofReal_measureReal (measure_ne_top m _)]; apply congrArg ENNReal.ofReal; by_cases e:x=1; · subst x; rw [show Iic (1:I)=Set.univ from Set.eq_univ_iff_forall.mpr (fun i=>i.property.2), measureReal_univ_eq_one]; rfl
 have E:x.val<1:= lt_of_le_of_ne x.property.2 (fun h=> e (Subtype.ext h)); have p:x.val ≥ 0:= x.property.1; unfold m; rw [show (μ.map v).real (Iic x)=μ.real (v ⁻¹' Iic x) from congrArg ENNReal.toReal (Measure.map_apply t measurableSet_Iic)]
 let A:=v ⁻¹' Iic x; apply le_antisymm
 · by_contra! k; obtain ⟨y,u,Y⟩:= exists_between (show x.val < μ.real A from k); have T:= measureReal_le_one (μ:=μ) (s:=A); obtain ⟨b,h⟩:= hx y (p.trans_lt u) (Y.trans_le T)
   have c:μ.real A ≤ g b:= by rw [show g b= μ.real (Iic b) from ProbabilityTheory.cdf_eq_real μ b]; exact measureReal_mono (fun i (v:g i≤x.val) => show i ≤ b from (lt_of_not_ge fun w=> u.not_ge (h ▸ (g.mono w).trans v)).le)
   rw [h] at c; exact c.not_gt Y
 by_cases t:0 < x.val; swap; · exact (le_of_not_gt t).trans measureReal_nonneg
 obtain ⟨b,k⟩:= hx _ t E; have u:μ.real (Iic b)≤μ.real A:= measureReal_mono (fun i (v:i≤ b)=> show g i ≤ x.val from k ▸ g.mono v)
 rw [← ProbabilityTheory.cdf_eq_real] at u; exact ge_trans u k.ge
-- fallback for S=∅ outside NoAtoms condition. same for different M with identical law.
variable {Y:Type*} [Nonempty Y] [MeasurableSpace Y] [StandardBorelSpace Y]
lemma samplerY(ν:Measure Y)[IsProbabilityMeasure ν](μ:Measure ℝ)[IsProbabilityMeasure μ][NullSingletonClass μ]:∃ g:ℝ→Y,MeasurePreserving g μ ν :=by obtain ⟨x,X⟩:= hMap μ; obtain ⟨f,H⟩:=ν.exists_measurable_map_eq; exact ⟨f∘x,(show MeasurePreserving f volume ν from ⟨H.1,H.2⟩).comp X⟩
end YM.CF.VolumeCape.Borel
