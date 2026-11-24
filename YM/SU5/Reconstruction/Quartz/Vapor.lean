import YM.SU5.Reconstruction.Quartz.League
import YM.SU5.Reconstruction.Vermont.Seam
/-! # Projections in the Mink sector and $p$-rank economy -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Ship
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame Clasp BridgeClub Anvil Waltz Submodule Complex Multiplier
open scoped Topology InnerProductSpace Complex Interval BigOperators Classical
local notation "N"=> Complex.re ⁻¹' (Set.Ici 0)
local notation "M"=> Complex.re ⁻¹' (Set.Ioi 0)
-- spectral gluing
lemma joinRoof (F:ℂ→ℂ) (h:ContinuousOn F N) (R:AnalyticOnNhd ℂ F M) (a b:ℝ)(p:a<b)(v:∀x∈Ioo a b,F ((x:ℂ)*Complex.I)=0) : EqOn F 0 (Complex.re ⁻¹' (Ici 0)):= by
 let U:= Complex.im ⁻¹' Ioo a b; let g(z:ℂ):= if 0≤ z.re then F z else 0; let L:= Complex.re ⁻¹' Iio 0
 have hm:IsOpen M:= isOpen_Ioi.preimage continuous_re; have hl:IsOpen L:= isOpen_Iio.preimage continuous_re; have hu:IsOpen U:= isOpen_Ioo.preimage continuous_im
 have up(z:ℂ)(u:z∈ M):g =ᶠ[𝓝 z] F := (show ∀ᶠ t in 𝓝 z, t∈ M from hm.mem_nhds u).mono fun i p=> if_pos (le_of_lt (show 0< i.re from p))
 have lo(z:ℂ)(u:z∈ L): g =ᶠ[𝓝 z] 0:= (show ∀ᶠ t in 𝓝 z,t∈L from hl.mem_nhds u).mono fun i p=> if_neg (show ¬ 0≤ i.re from not_le.mpr p)
 have hx:ContinuousOn g U:= by
   intro x q; rcases lt_trichotomy x.re 0 with h0|h0|h0
   · exact (continuousAt_const (y:=(0:ℂ))|>.congr (lo x h0).symm).continuousWithinAt
   · have p1:x∈ N:=h0.ge; have t0:= h x p1; have gy:g x=F x:=if_pos h0.ge; have he:F x=0:= Eq.trans (congrArg F (show x=(x.im:ℂ)*I from Complex.ext (by simp [h0]) (by simp))) (v x.im q)
     rw [Metric.continuousWithinAt_iff] at * -- tune
     intro ε e; obtain ⟨δ,q,r⟩:= t0 ε e; refine ⟨δ,q,fun {_} h k=>?_⟩; rw[gy]; unfold g; split; rename_i h; exact r h k; simpa [he]
   exact ((R x h0).continuousAt.congr (up x h0).symm).continuousWithinAt
 have hc:= Lens.seam_cement (t:=0) (fun z _ e=> (lt_or_gt_of_ne e).elim (fun p=> DifferentiableAt.congr_of_eventuallyEq (differentiableAt_const _) (lo z p)) (fun p=>(R z p).differentiableAt.congr_of_eventuallyEq (up z p))) hx hu
 obtain ⟨t,r,q⟩:=exists_between p; let z:ℂ:=⟨1,t⟩; let w:ℂ:=⟨-1,t⟩; have hz:z∈U:=⟨r,q⟩; have hw:w∈ L:= show (-1:ℝ)<0 from neg_one_lt_zero; have k:z∈ M:= show (0:ℝ)<1 from zero_lt_one
 have heq:EqOn g 0 U:= (hc.analyticOnNhd hu).eqOn_zero_of_preconnected_of_eventuallyEq_zero ((show Convex ℝ U from (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear a).inter (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear b)).isPreconnected) (show w∈U from ⟨r,q⟩) (lo w hw)
 have he: EqOn F 0 M:= R.eqOn_zero_of_preconnected_of_eventuallyEq_zero ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected) k ((up z k).symm.trans (Eventually.mono (hu.mem_nhds hz) heq)) -- arg tune
 exact he.of_subset_closure h continuousOn_const (preimage_mono Ioi_subset_Ici_self) (by rw [closure_preimage_re, closure_Ioi]) -- tune
variable {H:Hilbert}{a:Axis}(b:Axis)(u t:ℝ)(S:OS.Semigroup H a)
local notation "U"=> Picket.trans S
local notation "τ" => Picket.head a b
-- price in H_a light from positive.Solve using columns_hol
lemma polaris (e:u=1 ∨ u= -1)(p:Paces b S)(V:Submodule ℂ H)(c:IsClosed (V:Set H)) (y:H)(x z:ℝ)(d:x<z) (h:∀v∈Ioo x z,U (v • (Picket.head a b u)) y ∈ V): U (t • (τ u)) y∈ V:= by
 let A(p:ℂ):= column S b u p; let j(t:ℝ):=(↑(-t):ℂ)*I
 have hr(t:ℝ): A (j t)= U (t • τ u):= by
    rw [← shift b u t S p e]; unfold A column concern; congr 1; ext1 x; unfold Chirp.slopeRay Function.comp sound j; congr 1; push_cast; ring
 rw [←hr]; letI : CompleteSpace V:= c.completeSpace_coe
 rw [show V= Vᗮᗮ from (by rw [Submodule.orthogonal_orthogonal_eq_closure]; exact Submodule.ext (fun x=> Set.ext_iff.mp c.closure_eq x|>.symm) )] -- syntax
 intro v w; let F(z:ℂ):= inner ℂ v (A z y); have he:F (j t)=0:= by
    refine joinRoof F (fun z (t:0≤z.re)=>?_) (fun t p=> ?_) (-z) (-x) (neg_lt_neg d) ?_ (show j t ∈ N from ge_of_eq (by simp[j] : (j t).re=0)) -- tune
    · exact Tendsto.inner tendsto_const_nhds (column_dawn b u S (𝓝[N] z) id (show ∀ᶠ i in _,0≤(id i:ℂ).re from self_mem_nhdsWithin) t nhdsWithin_le_nhds y)
    · exact (( (innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ H y)).analyticAt _).comp (columns_hol b u S t p)
    intro r k; rw [show (r:ℂ)*I=j (-r) from (by unfold j;rw [neg_neg])]; unfold F; rw [hr]; exact Submodule.inner_left_of_mem_orthogonal (h (-r) (neg_mem_Ioo_iff.mpr k)) w -- tune order
 exact he
end YM.Quartz.Ship
