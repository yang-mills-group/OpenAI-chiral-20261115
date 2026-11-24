import GaugeFieldConstruction.Cable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-
# Mask for arbitrary open dense grids. All coordinates move with frames.Joint θ.Covers costs on all Conf.
 NOTE Does not approach f in Test topology! for price comparison in Poll estimator, actual hierarchy exists and is regular on Conf first. Need avoid partial tie gates at finite prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ} {C:Set (Points n)}
structure RazorPV (C:Set (Points n)) where
 L:ℕ→ Test n →ₗ[ℂ] Test n
 small : ∀ i f, tsupport (L i f)⊆ tsupport f
 tiny : ∀ i f,tsupport (L i f)⊆ C
 slope : ∀ i f x,‖L i f x‖ ≤ ‖f x‖
 stat : ∀ x∈ C,∀ᶠ i in atTop,∀ f,L i f x=f x

lemma LenscapPV (p:IsOpen C):Nonempty (RazorPV C):=by
 classical
 obtain ⟨X,hh,U,T⟩ : ∃ X:Points n→ℝ,support X=C ∧ ContDiff ℝ ∞ X ∧ Set.range X⊆ Set.Icc 0 1:= p.exists_contDiff_support_eq
 let g (i:ℕ)(x:Points n):ℝ:=Real.smoothTransition ((i:ℝ)*X x-1)
 have S(i): ContDiff ℝ ∞ (g i):= Real.smoothTransition.contDiff.comp ((contDiff_const.mul U).sub contDiff_const) -- tune namespace
 have w(i:ℕ): tsupport (g i)⊆ C:=by
    let A:= ((fun x=>(i:ℝ)*X x)⁻¹' (Set.Ici 1))
    have k:IsClosed A:= isClosed_Ici.preimage (continuous_const.mul U.continuous)
    apply Set.Subset.trans (b:=A) _ ?_
    · apply closure_minimal _ k; intro x hx
      change g i x ≠ 0 at hx; unfold g at hx
      exact (sub_pos.mp (lt_of_not_ge fun p=> hx (Real.smoothTransition.zero_of_nonpos p))).le
    intro x hx; rw[←hh]; intro b
    have e:X x=0:=b; change 1≤ (i:ℝ)*X x at hx; rw [e,mul_zero] at hx; exact not_le_of_gt zero_lt_one hx
 refine ⟨⟨fun i=> weigh _ (S i),fun i f=> taxed ..,fun i f=>?_,?_,?_⟩⟩
 · apply Subset.trans ?_ (w i); exact tsupport_smul_subset_left _ _
 · intro i f x; rw [scalar,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
 intro x hx; have h:X x≠0:= by exact (show x∈ support X from hh.symm ▸ hx)
 have k: 0<X x:= lt_of_le_of_ne (T (mem_range_self _)).1 (Ne.symm h)
 filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((2:ℝ)/X x))] with i t f
 have e:1 ≤ (i:ℝ)*X x-1 := by
   have h:2≤ (i:ℝ)*X x:= (div_le_iff₀ k).mp t; linarith
 change weigh _ _ _ _= _; rw[scalar, show g i x=1 from Real.smoothTransition.one_of_one_le e,one_smul]

variable (Q:RazorPV C) (hC:∀ᵐ x:Points n,x∈C)
def cautionPV {F:Points n→ℂ} : Prop:= ∀ p:Test n, Integrable (fun i=> p i * F i)
variable (F:Points n→ℂ)
include hC
lemma RazorMintPV (p:cautionPV (F:=F)) (x:Test n): Tendsto (fun i=> (Q.L i x).applyTo F) atTop (𝓝 (x.applyTo F)):=by
 unfold Test.applyTo
 refine tendsto_integral_of_dominated_convergence (fun z=>‖x z*F z‖) (fun i=> (p (Q.L i x)).aestronglyMeasurable) (p x).norm (fun i=>Eventually.of_forall ?_) ?_
 · intro z; simp_rw [norm_mul]; exact mul_le_mul_of_nonneg_right (Q.slope i x z) (norm_nonneg _)
 filter_upwards [hC] with x' hx; exact tendsto_const_nhds.congr' ((Q.stat x' hx).mono fun i p=> congr_arg (· * F x') (p x).symm)
#print axioms RazorMintPV
end YM.GaugeFieldConstruction.Fathom
