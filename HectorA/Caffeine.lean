import HectorA.Trifles
import YM.Heat.Extend
set_option autoImplicit false
noncomputable section
namespace Yoland
open YM Filter Set Function
open YM.OS YM.OS.Semigroup
open scoped Topology NNReal InnerProductSpace BigOperators Classical
variable {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)(x:H)
-- Real inst check
set_option synthInstance.maxSize 18000
attribute [local instance] InnerProductSpace.complexToReal
-- Complex.SInt type not isScalarTower. add
#synth ∀ X:Hilbert, NormedSpace ℝ X
abbrev tempo (t:ℝ):H:= S.E t.toNNReal x
private lemma authentic(t:ℝ)(h:0<t): AnalyticAt ℝ (tempo S x) t:=by
 let f (z:ℂ):= S.F z x
 have hp: AnalyticAt ℂ f t:= ((ContinuousLinearMap.apply ℂ H.space x).analyticAt _).comp (S.localHeat t (show 0 < (t:ℂ).re from h))
 refine ((AnalyticAt.restrictScalars (𝕜:=ℝ) hp).comp (Complex.ofRealCLM.analyticAt t)).congr ?_
 filter_upwards [lt_mem_nhds h] with y hy
 change S.F y x=_; rw [show (y:ℂ) = duration y.toNNReal from congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal y hy.le).symm,S.roots_heat (Real.toNNReal_pos.mpr hy)]
lemma civilB: Civil (tempo S x):=by
 refine ⟨authentic S x, fun t ht=>⟨S.E t.toNNReal,fun a ha=> ?_⟩⟩
 unfold tempo; rw [show (a+t).toNNReal=t.toNNReal+a.toNNReal from (by apply NNReal.eq; rw [Real.coe_toNNReal _ (by linarith),NNReal.coe_add,Real.coe_toNNReal _ ht.le,Real.coe_toNNReal _ ha.le,add_comm]),S.time]; rfl
lemma continuousTempo:Continuous (tempo S x):= (S.continuousE x).comp continuous_real_toNNReal
abbrev detail(i:ℕ)(t:ℝ):H:= iteratedDeriv i (tempo S x) t
lemma clear (Q: ¬FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun t:ℝ≥0=> S.E t x)))) (a:ℝ)(p:0<a)(n:ℕ): LinearIndependent ℂ (fun i:Fin n=> detail S x (i.val+1) a):=by
 by_contra h
 obtain ⟨K,i,y⟩:=package (tempo S x) a (civilB S x) p h
 have hc : IsClosed (K:Set H.space):= K.closed_of_finiteDimensional
 have hv : closure (Set.Ioi (0:ℝ)) ⊆ (tempo S x) ⁻¹' (K:Set H.space):= closure_minimal y (hc.preimage (continuousTempo ..))
 rw [closure_Ioi] at hv
 apply Q
 refine FiniteDimensional.of_injective (Submodule.inclusion (show (Submodule.span ℂ (Set.range (fun t:ℝ≥0=> S.E t x)))≤K from ?_)) (Submodule.inclusion_injective _)
 rw [Submodule.span_le]; rintro _ ⟨l,rfl⟩; simpa [tempo] using hv (show (l:ℝ) ∈ Ici (0:ℝ) from l.property)
#check FiniteDimensional.of_injective
#check IsScalarTower
end Yoland
