import YM.SU5.SatinWard.Resolution.Peralta
import YM.SU5.SatinWard.Resolution.Moonglow
import YM.SU5.Reconstruction.Seams.Bills
import YM.SU5.Macro.Across

/-!
# A universal time till

Price a complex heat lag, in operator norm, from positive Eu-time steps
costed on just a specified open interval. Affine stencil. Coefficients
and certification can be taken independently not just of the Minkowski
moments we will estimate but also of the energy operator (works on every
support including at arbitrarily high energies).
-/
noncomputable section
namespace YM.LocalFieldBounds.Easel
open Function Set Filter Topology
open OS OS.Semigroup
open scoped NNReal Topology
open ConePrice.Sail

namespace Stair


abbrev Stone := (Set.Icc (0:ℝ) 1 : Type)

def boost (z : ℂ) : C(Stone,ℂ) := if h : z ∈ inside then
  ⟨fun x => ((x:ℝ):ℂ)^z,
    continuous_iff_continuousAt.mpr fun x =>
      (Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (show 0 ≤ ((x:ℝ):ℂ).re from x.property.1)) h).comp (f:=fun x : Stone => ((x:ℝ):ℂ))
        (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt⟩
  else 0

lemma reach {z : ℂ} (h : z ∈ inside) (x : Stone) :
    boost z x = ((x:ℝ):ℂ)^z := by
  unfold boost; rw [dif_pos h]; rfl

lemma enduring : ContinuousOn boost inside := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [show uncurry (fun (x : inside) y => (inside.restrict boost x) y) =
    (fun x : inside × Stone => ((x.2:ℝ):ℂ) ^ (x.1:ℂ)) from funext fun x => reach x.1.property x.2]
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  exact ContinuousAt.comp
    (g := fun p : ℂ × ℂ => p.1 ^ p.2)
    (f := fun x : inside × Stone => (((x.2:ℝ):ℂ), (x.1:ℂ)))
    (Complex.continuousAt_cpow_of_re_pos (Or.inl x.2.property.1) x.1.property)
    (by fun_prop)

lemma universal : AnalyticOnNhd ℂ boost inside := by
  let P (i : Stone) : C(Stone,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ i
  refine Analysis.lift_weak (Set.range P)
    (fun _ _ h => ContinuousMap.ext fun i => h (P i) (mem_range_self i))
    open_inside enduring ?_
  rintro _ ⟨x,rfl⟩
  refine (DifferentiableOn.congr (f := fun z : ℂ => ((x:ℝ):ℂ)^z) ?_ (fun p hp => reach hp x))
  by_cases h : ((x:ℝ):ℂ)=0
  · simp only [h]
    apply differentiableOn_const (c:=(0:ℂ)) |>.congr
    rintro z hz
    refine Complex.zero_cpow ?_
    rintro rfl; exact lt_irrefl (0:ℝ) hz
  exact (differentiable_id.const_cpow (Or.inl h)).differentiableOn

end Stair

open Stair

/-- Finite linear combination. -/
structure Stamp (u v : ℝ) where
  Job : Type
  list : Fintype Job
  fee : Job → ℂ
  step : Job → Set.Ioo u v
  normalized : ∑ i : Job, fee i = 1

attribute [instance] Stamp.list

namespace Stamp
variable {u v : ℝ}

def Covers (r : Stamp u v) (z : ℂ) (e : ℝ) : Prop :=
  ‖(∑ i, r.fee i • boost (r.step i).val) - boost z‖ < e

local notation "I" => Set.Ioo u v

private theorem chips (a : I) (hu : 0 ≤ u) (z : ℂ) (hz : z ∈ inside)
    (e : ℝ) (he : 0 < e) :
    ∃ w : I →₀ ℂ,
      ‖(∑ i ∈ w.support, w i • (boost i.val - boost a.val)) -
        (boost z - boost a.val)‖ < e := by
  let d (t : ℂ) := boost t - boost a.val
  let f (x : I) := d x.val
  let Y := Submodule.span ℂ (Set.range f)
  let N := Y.topologicalClosure
  letI : IsClosed (N:Set C(Stone,ℂ)) := Y.isClosed_topologicalClosure
  have h : EqOn (N.mkQL ∘ d) (fun _ => 0) inside :=
    pioneer ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected)
      (show (a.val:ℂ) ∈ inside from hu.trans_lt a.property.1)
      u v a.property
      (fun t ht => (@ContinuousLinearMap.analyticAt ℂ _ C(Stone,ℂ) _ _ (C(Stone,ℂ) ⧸ N) _ _ N.mkQL _).comp (show AnalyticAt ℂ d t from (universal t ht).sub analyticAt_const))
      analyticOnNhd_const (fun x hx => (Submodule.Quotient.mk_eq_zero _).2
        (Y.le_topologicalClosure (Submodule.subset_span (show f ⟨x,hx⟩ ∈ Set.range f from mem_range_self _))))
  have hz' : d z ∈ closure (Y:Set C(Stone,ℂ)) :=
    (Submodule.Quotient.mk_eq_zero N).1 (h hz)
  obtain ⟨q,hq,hqd⟩ := Metric.mem_closure_iff.1 hz' _ he
  change q ∈ Submodule.span ℂ (Set.range f) at hq
  rw [← Finsupp.range_linearCombination] at hq
  obtain ⟨s,rfl⟩ := hq
  exact ⟨s, by rw [dist_comm, dist_eq_norm, Finsupp.linearCombination_apply] at hqd; exact hqd⟩

theorem afforded (hu : 0 ≤ u) (h : u < v) (z : ℂ) (hz : z∈inside)
    (e : ℝ) (he : 0 < e) :
    ∃ t : Stamp u v, t.Covers z e := by
  obtain ⟨x,hx⟩ := nonempty_Ioo.2 h
  obtain ⟨w,m⟩ := chips ⟨x,hx⟩ hu z hz e he
  let P := Option (w.support)
  let f : P → I := fun i => Option.rec ⟨x,hx⟩ Subtype.val i
  let s : P → ℂ :=
    fun i => Option.rec (1-(∑ a : w.support, w a.val)) (fun a => w a.val) i
  have q : ∑ i, s i = 1 := by rw [Fintype.sum_option]; exact sub_add_cancel _ _
  refine ⟨⟨P,inferInstance,s,f,q⟩,?_⟩
  change ‖(∑ i, s i • boost (f i).val) - boost z‖ < e
  rw [Fintype.sum_option]
  change ‖(1-(∑ a : w.support, w a.val)) • boost x
    + (∑ a : w.support, w a.val • boost a.val.val) - _‖ < _
  convert m using 2
  conv_rhs => rw [←Finset.sum_coe_sort]
  rw [sub_smul (1:ℂ) (∑ a : w.support, w a.val) (boost x),
    one_smul ℂ (boost x), Finset.sum_smul (f:=fun a : w.support => w a.val) (x:=boost x) (s:=Finset.univ)]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

variable {H : Hilbert} {a : Axis} (S : Semigroup H a)
variable (C : Stamp u v)
set_option quotPrecheck false
local notation "λ₀" i:max => ((C.step i).val:ℂ)

lemma roots_paid (hu : 0 ≤ u) (z : ℂ) (hz : z∈inside) :
    ‖(∑ i, C.fee i • S.roots (λ₀ i)) - S.roots z‖ ≤
      ‖(∑ i, C.fee i • boost (λ₀ i)) - boost z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  obtain ⟨r,hr,h,e⟩ := S.at_root x.property
  let y : Stone := ⟨r,hr,h⟩
  have f (w : ℂ) (hw : w∈inside) : S.roots w x = boost w y := by
    rw [S.on_root hw, e, reach hw]
  have d := ContinuousMap.norm_coe_le_norm ((∑ i, C.fee i • boost (λ₀ i)) - boost z) y
  simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply] at d ⊢
  have u (i) := f (λ₀ i) (hu.trans_lt (C.step i).property.1)
  simp_rw [f z hz, u]
  exact d

abbrev expense := ∑ i, C.fee i • S.E (C.step i).val.toNNReal

lemma interpolate (hu : 0 ≤ u) (z : ℂ) (hz : z ∈ inside) {e : ℝ}
    (h : C.Covers z e) :
    ‖expense S C - phase S z‖ < e := by
  have p (i) : S.E (C.step i).val.toNNReal = S.F (λ₀ i) :=
    (width_real _ _).symm.trans (phase_meets S (show (λ₀ i) ∈ inside from hu.trans_lt (C.step i).property.1))
  unfold expense
  simp_rw [phase_meets S hz, p, OS.Semigroup.F]
  let V : C(spectrum ℂ (S.E 1),ℂ) →⋆ₐ[ℂ] H.Op := cfcHom (S.stare 1).isStarNormal
  have eq : (∑ i, C.fee i • V (S.roots (λ₀ i))) - V (S.roots z) =
      V ((∑ i, C.fee i • S.roots (λ₀ i)) - S.roots z) := by
    rw [map_sub, map_sum]
    simp only [map_smul]
  rw [eq,(isometry_cfcHom _ (S.stare 1).isStarNormal).norm_map_of_map_zero (map_zero _)]
  exact (roots_paid S C hu z hz).trans_lt h

#print axioms interpolate
end Stamp
end YM.LocalFieldBounds.Easel
