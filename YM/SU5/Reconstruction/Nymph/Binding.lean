import YM.SU5.Selected.Halo
import YM.SU5.FiniteGaugeData.Tower.Alliance

/-!
# Preserve localized trace via projection and real continuation
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function MeasureTheory Germ Set Filter SelectionAnalysis InnerProductSpace Metric Submodule
open scoped Topology InnerProductSpace NNReal ENNReal
namespace SkyFold
variable {G:AddSubgroup ℝ} {H:Hilbert} {I:Type*} {P:Players G H}
variable {f f':H.Op}
-- Two separate ways to monetize subspaces: heat/inverse continuity and small-shift envelope
lemma priced {W U: Submodule ℂ H} (w:IsClosed (W:Set H))
    (h: Set.MapsTo f U W) : Set.MapsTo f U.topologicalClosure W := by
 intro x hx; exact closure_minimal h (w.preimage f.continuous) hx
lemma from_spans (T:H.Op){U:Set H}(J:Submodule ℂ H)(p:IsClosed (J:Set H))
    (h:Set.MapsTo T U J): Set.MapsTo T (span ℂ U).topologicalClosure J := by
 apply priced p (fun x hx=>?_)
 have hz: span ℂ U≤ J.comap T.toLinearMap:=by rw [span_le]; exact h
 exact hz hx

lemma commuting {J:Submodule ℂ H}[J.HasOrthogonalProjection](h:IsSelfAdjoint f)
    (k:Set.MapsTo f J J) : Commute f J.starProjection := by
 have he:Set.MapsTo f Jᗮ Jᗮ:= by
    intro x hx
    intro y hy
    change inner ℂ y (f x)=0
    rw [← show inner ℂ (f y) x=inner ℂ y (f x) from h.isSymmetric ..]
    exact inner_right_of_mem_orthogonal (k hy) (show _ from hx)
 ext1 x; let u:=J.starProjection x; let v:=Jᗮ.starProjection x; have hx : u + v=x:= J.starProjection_add_starProjection_orthogonal x
 have hp:u∈J:= starProjection_apply_mem ..; have hv:v∈Jᗮ:= starProjection_apply_mem ..
 change f u= J.starProjection (f x)
 rw [show f x=f u+f v from (congrArg f hx.symm).trans (map_add ..)]; rw [map_add, Submodule.starProjection_eq_self_iff.mpr (k hp),J.starProjection_apply_eq_zero_iff.mpr (he hv),add_zero] -- nth maybe
lemma commutes_in {J:Submodule ℂ H}[J.HasOrthogonalProjection](h:Commute f J.starProjection): Set.MapsTo f J J:= by
 intro x p
 apply (J.starProjection_eq_self_iff).mp
 rw [show J.starProjection (f x)=f (J.starProjection x) from congrArg (fun W:H.Op=> W x) h.symm.eq, Submodule.starProjection_eq_self_iff.mpr p]
lemma noexit {a:Axis} (P:OS.Semigroup H a) (J:Submodule ℂ H) [J.HasOrthogonalProjection]
    (h:Set.MapsTo (P.E 1) J J) (t:ℝ) : Set.MapsTo (P.edge t) J J := commutes_in (lamp_orbit P (commuting (show IsSelfAdjoint _ from P.sym _) h) t)
lemma sector_under_focus {J:Submodule ℂ H}(p : IsClosed (J:Set H)) (u:H)(h:u∈J)
    (k: ∀ᶠ i in 𝓝 (0:G), P.play i u∈ J) : P.pi_c u ∈ J:= by
 have hz : P.pi_c u∈ Jᗮᗮ:=by
   intro x hx; change inner ℂ x (P.pi_c u)=0; rw [show inner ℂ x (P.pi_c u)=inner ℂ x u from P.retain (innerSL ℂ x) u ?_]; exact inner_left_of_mem_orthogonal h hx
   change ContinuousAt (fun i=>inner ℂ x (P.play i u)) _; refine (continuousAt_const («y»:= (0:ℂ))).congr ?_; exact (k.mono fun i hi=> (inner_left_of_mem_orthogonal hi hx).symm)
 rw [orthogonal_orthogonal_eq_closure] at hz; exact p.closure_subset_iff.mpr Set.Subset.rfl hz
end SkyFold
end YM.CF.Buffered.Afterglow.Tower
