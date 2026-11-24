import YM.CF.BProof.Floral.Hol
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology NNReal ENNReal
namespace YM.CF.Floral
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]{D:Set ℂ}{C:ℝ}
theorem cord {X:Type*}[MeasurableSpace X](μ:Measure X)[IsFiniteMeasure μ]{F:ℂ→X→E}
    (d:IsOpen D)(H:∀ x, Hol D fun z=> F z x)(p:∀ z∈D, Integrable (F z) μ)(w:∀ z∈D,∀ᵐ x∂μ,‖F z x‖≤C) : Hol D fun z=>∫ x,F z x∂μ:=by
 classical
 intro z hz
 obtain ⟨r,g,M⟩:=nhds_basis_closedBall.mem_iff.mp (d.mem_nhds hz); let V:= ball z (r/2)
 have he(y)(v:y∈V): closedBall y (r/2) ⊆ D:=fun t l=> M (mem_closedBall.mpr (by have h:=dist_triangle t y z; have hb:=mem_ball.mp v; have hv:=mem_closedBall.mp l; linarith))
 have hw:V⊆D:=fun y v=> he y v (mem_closedBall_self (by linarith)); have hk:= d.mem_nhds hz; let K(t:ℂ)(x):=deriv (fun z=> F z x) t
 have hm(x)(t)(p:t∈D):HasDerivAt (fun z=>F z x) (K t x) t:= ((H x).differentiableAt (d.mem_nhds p)).hasDerivAt
 have hi: AEStronglyMeasurable (K z) μ:=by
    let Q(t:ℂ) (x):= if t∈D then slope (fun v=>F v x) z t else 0
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z) (f:=Q) ?_ (ae_of_all _ fun x=>?_)
    · intro i; unfold Q; split
      next h=> exact ((p i h).aestronglyMeasurable.sub (p z hz).aestronglyMeasurable).const_smul _
      exact aestronglyMeasurable_const
    exact ((hm x z hz).tendsto_slope).congr' (Eventually.mono (mem_nhdsWithin_of_mem_nhds hk : ∀ᶠ y in 𝓝[≠] z,y∈D) fun t f=>(if_pos f).symm)
 have hg: ∀ᵐ x∂μ,∀ z∈D,‖F z x‖ ≤ C:=by
    letI : Nonempty D:= ⟨⟨z,hz⟩⟩; let y:=TopologicalSpace.denseSeq D
    filter_upwards [ae_all_iff.mpr (fun i:ℕ=>w (y i) (y i).property)] with x hx t g
    have he(u:D):‖F u x‖ ≤ C:= isClosed_property (TopologicalSpace.denseRange_denseSeq _) (p:=fun u:D => ‖F u x‖≤ C) (isClosed_le ((continuousOn_iff_continuous_restrict.mp (H x).continuousOn).norm) continuous_const) hx u
    exact he ⟨t,g⟩
 exact ((hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (s:=V) (ball_mem_nhds z (half_pos g)) ((show ∀ᶠ z in 𝓝 z,z∈D from hk).mono fun x v=> (p x v).aestronglyMeasurable) (p z hz) hi (hg.mono fun x g'=> fun y v=> c_deriv (H x) (half_pos g) (he y v) g') (integrable_const (C/(r/2))) (ae_of_all _ fun i=> fun y v=> hm i y (hw v))).2.differentiableAt).differentiableWithinAt
end YM.CF.Floral
