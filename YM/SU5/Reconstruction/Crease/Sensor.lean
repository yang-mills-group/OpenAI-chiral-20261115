import YM.SU5.Reconstruction.Anvil.OpCoin
import YM.SU5.Reconstruction.Crease.Ghost
/-! # weak limits. Anti & * -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap OS Semigroup Anvil
open scoped Topology BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert} {ι:Type*}{p:Filter ι}[NeBot p]{A:ι→H.Op}{B:H.Op}
-- aperture. WOT with operators unif.
omit [NeBot p]
lemma star_Limited (h:Limited p A B): Limited p (star A) (star B):=by
 refine ⟨?_,fun x y=>?_⟩
 · simpa using h.uniform
 let t:=(h.confirms y x).star
 have he(M:H.Op):inner ℂ x (star M y)=star (inner ℂ y (M x)):=  (adjoint_inner_right M x y).trans (inner_conj_symm (M x) y).symm

 simpa only [Pi.star_apply,he] using t
lemma shade_Limited (J:Flash H)(h:Limited p A B): Limited p (fun i=> J.shade (A i)) (J.shade B):=by
 refine ⟨by simpa only [J.shade_cost] using h.uniform,fun x y=> ?_⟩
 have e(i:H.Op): inner ℂ x (J.shade i y)=star (inner ℂ (J.f x) (i (J.f y))):= by
    rw [J.shade_at]; conv_lhs=> lhs; rw [← J.twice x]
    exact (J.light _ _).trans (inner_conj_symm (i (J.f y)) (J.f x)).symm -- check order of lemma
 simpa only [e] using (h.confirms (J.f x) (J.f y)).star
end YM.BridgeClub
