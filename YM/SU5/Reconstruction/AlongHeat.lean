/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.Heat.Duration
/-!
# Intertwining all Euclidean heat implies intertwining interior holomorphic and edge group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {A B : Hilbert} {a b : Axis} (S : Semigroup A a) (T : Semigroup B b) (L : A →L[ℂ] B)
variable (h : ∀ t : ℝ≥0, ∀ x : A, L (S.E t x) = T.E t (L x))

-- identity argument as in `YM/Heat/Extend` / `Selected/Edges`
include h
lemma intertwines_F (x : A) {z : ℂ} (hz : z∈inside) : L (S.F z x) = T.F z (L x) := by
  let f : ℂ → B := fun z => L (S.F z x)
  let g : ℂ → B := fun z => T.F z (L x)
  have hf : AnalyticOnNhd ℂ f inside := fun z p =>
    (L.comp (ContinuousLinearMap.apply ℂ A.space x)).analyticAt (S.F z) |>.comp (S.localHeat z p)
  have hg : AnalyticOnNhd ℂ g inside := fun z p =>
    (ContinuousLinearMap.apply ℂ B.space (L x)).analyticAt _ |>.comp (T.localHeat z p)
  suffices p : EqOn f g inside from p hz
  refine hf.eqOn_of_preconnected_of_frequently_eq hg
    (convex_halfSpace_gt reCLM.toLinearMap.isLinear 0 |>.isPreconnected) (z₀:=duration 1) (dur.mpr zero_lt_one) ?_
  intro p
  have hv : Tendsto duration (𝓝[>] (1:ℝ≥0)) (𝓝[≠] duration 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with i hi
    change ¬duration i = _; exact fun q => (mem_Ioi.mp hi).ne' (Subtype.ext (Complex.ofReal_injective q))
  obtain ⟨i,w,v⟩ := ((hv.eventually p).and self_mem_nhdsWithin).exists
  have hw : 0 < i := zero_lt_one.trans (mem_Ioi.mp v)
  exact w (show f (duration i)=g (duration i) from by unfold f g; rw [S.roots_heat hw,T.roots_heat hw,h])

lemma intertwines_edge (x : A) (z : ℝ) : L (S.edge z x) = T.edge z (L x) := by
  refine congrFun ((S.whole 1).equalizer (L.continuous.comp (S.edge z).continuous)
    ((T.edge z).continuous.comp L.continuous) ?_) x
  funext w
  dsimp only [Function.comp_apply]
  rw [h,S.high,T.high]
  exact S.intertwines_F T L h _ (length.mpr zero_lt_one)
end YM.OS.Semigroup
