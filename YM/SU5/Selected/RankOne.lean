import YM.SU5.Selected.Fault
/-! Select rank-one joint invariant space for almost every compression character. Measure
class that will be supplied from the vector state. Later transfer all observables & time operators. -/

set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
open Function Filter Set Topology NormedSpace MeasureTheory Measure ContinuousMap WeakDual
open scoped Topology InnerProductSpace BigOperators NNReal ENNReal ComplexOrder
variable {A B W : Type*} [CommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {D:Submodule ℂ W} [CompleteSpace D]

open Submodule Metric
namespace Transaction
variable (T : Transaction A B D)
local notation "π"=> D.starProjection
local notation "μ"=> D.orthogonalProjectionOnto
local notation "ι"=> D.subtypeL
local notation "Ω"=> T.original.val
local notation "S"=> T.station
local notation "C"=> T.corner

-- The span subalgebra currencies allow explicit approximation before any
-- component selection. Use exact projection id of `grounds` and cyclic vectors.
noncomputable def spends : B →ₗ[ℂ] W := ((ContinuousLinearMap.apply ℂ W Ω).toLinearMap.comp (S).toAlgHom.toLinearMap) -- syntax
lemma spendsVal(b:B): T.spends b=S b Ω:=rfl
lemma projected(b: T.effort): π (S b.val Ω)=0 := by
  let p:=T.original
  change ι (μ (S b.val Ω)) = _
  rw [←T.matchVal b.val T.original,T.unmarked,map_zero]; simp
lemma almost (b:B) {ε:ℝ}(p:0< ε): ∃ c:T.effort, (inner ℂ T.original (C (T.off_square (b-c.val)) T.original)).re < ε := by
  let Z:Submodule ℂ W:= T.effort.map T.spends
  have h : Zᗮ ≤ D:= by
    intro x hx; apply (T.grounds x).2; intro a p
    apply T.searches.eq_of_inner_right ℂ; intro t
    have he: T.spends (star a*t-t)∈ Z:= ⟨_,show _∈T.effort from subset_span (show _∈_ from ⟨star a,T.star_move a p,t,rfl⟩),rfl⟩
    have hv:= inner_right_of_mem_orthogonal he hx; rw [map_sub,inner_sub_left,spendsVal,spendsVal,map_mul,map_star] at hv
    have hw : inner ℂ ((S a).adjoint (S t Ω)) x=inner ℂ (S t Ω) x := sub_eq_zero.mp hv
    rwa [ContinuousLinearMap.adjoint_inner_left] at hw
  let x:= S b Ω; let y:= π x
  have he : x-y∈ closure (Z:Set W) := by
    change _∈Z.topologicalClosure; rw [← orthogonal_orthogonal_eq_closure]
    exact orthogonal_le h (sub_starProjection_mem_orthogonal x)
  obtain ⟨i,⟨c,u,hc⟩,hi⟩ := mem_closure_iff.mp he (Real.sqrt ε) (Real.sqrt_pos.2 p) -- picks metric? mathlib conflict!
  let e:T.effort:=⟨c,u⟩
  have hv:= T.price (b-c)
  have hw: S (b-c) Ω = x-i := by rw [map_sub]; exact congrArg (x-·) hc
  have ht:(π) i=0:= by rw [←hc]; exact T.projected e
  rw [hw,map_sub,ht,sub_zero] at hv
  refine ⟨e,?_⟩; change (inner ℂ _ _).re < ε; change (inner ℂ _ (C (T.off_square (b-c)) _)).re < ε
  rw [←hv,show x-i-(π) x=(x-y)-i from by unfold y; abel]
  rw [dist_eq_norm] at hi
  nlinarith [Real.sq_sqrt p.le, norm_nonneg (x-y-i)]

variable [MeasurableSpace (Resident A)][BorelSpace (Resident A)](P:Measure (Resident A)) [IsFiniteMeasure P]
structure Bary : Prop where
 use_char (a:A) : (∫ x, eye x a ∂P)=inner ℂ T.original (T.corner a T.original)

variable (H : T.Bary P)
include H
-- Markov estimate, valid for each b. Use outer bound, avoid needing measurability of exists-c.
lemma thin (b:B) (ε:ℝ) (p:0<ε) : ∀ᵐ x ∂P, ∃ c:T.effort, (eye x (T.off_square (b-c.val))).re < ε:=by
  let f (c:T.effort) (x:Resident A):= (eye x (T.off_square (b-c.val))).re
  let A' := {x | ¬∃c,f c x<ε}
  rw [ae_iff]
  change P A'=0
  by_contra h
  have hz: 0< P.real A':= ENNReal.toReal_pos h (measure_ne_top P A')
  obtain ⟨c,hc⟩:= T.almost b (mul_pos p hz)
  have hl:A' ⊆ {x| ε ≤ f c x}:= by intro x t; exact le_of_not_gt (fun h=> t ⟨c,h⟩)
  have ht:= Complex.continuous_re.comp (eyeline (T.off_square (b-c.val))); have F:(0: Resident A→ℝ) ≤ᵐ[P] f c := Eventually.of_forall fun x=> (sq_nonneg _).trans_eq (T.evaluate_price x (b-c.val)) -- trouble
  have hI: Integrable (fun x:Resident A=> eye x (T.off_square (b-c.val))) P:= (eyeline _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have Ie: (∫ x,f c x ∂P)=(inner ℂ T.original (C _ T.original)).re:= (integral_re hI).trans (congrArg Complex.re (H.use_char (T.off_square (b-c.val))))
  have L:= mul_meas_ge_le_integral_of_nonneg F (show Integrable (f c) P from ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ε
  rw [Ie] at L
  exact hc.not_ge ((mul_le_mul_of_nonneg_left (measureReal_mono hl) p.le).trans L)
omit H

lemma plays (x:Resident A) (w:(T.selected x).GNS) (σ:∀ u∈T.steps, implement (T.selected x) u w=w) (e:T.effort):
    inner ℂ (vectorForm (T.selected x) e.val) w=0:= by
  rcases e with ⟨e,g⟩; dsimp; let X:=T.selected x
  change inner ℂ (vectorForm X e) w=0; induction g using Submodule.span_induction with
  | mem m h=>
    obtain ⟨t,h,a,rfl⟩:=h
    rw [map_sub,inner_sub_left]
    change inner ℂ (implement X (t*a) (vector X)) w-_ = _; rw [map_mul]
    apply sub_eq_zero.mpr
    have hx:ContinuousLinearMap.adjoint (implement X t) w=w := by change star (implement X t) w=_; rw [←map_star]; exact σ _ (T.star_move t h)
    exact (ContinuousLinearMap.adjoint_inner_right (implement X t) _ w).symm.trans (congrArg (inner ℂ (vectorForm X a)) hx)
  | zero=> rw [map_zero,inner_zero_left]
  | add a b _ _ hx hy=> rw [map_add,inner_add_left,hx,hy,add_zero]
  | smul k a _ hx=> rw [map_smul,inner_smul_left,hx,mul_zero]
include H
lemma generically (x:ℕ→ B) (q:DenseRange x) : ∀ᵐ s∂P, T.FixedPhase s:=by
  let e (n:ℕ) := (1/2:ℝ)^n; have p(n):0<e n:= pow_pos (by norm_num) _
  have ht:Tendsto e atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have Hf := ae_all_iff.mpr fun i:ℕ=> ae_all_iff.mpr fun j:ℕ=> T.thin P H (x i) (e j) (p j)
  filter_upwards [Hf] with X Xv
  intro v a; let ψ := T.selected X; let ω := vector ψ
  let c:= inner ℂ ω v; let w:= v - c • ω
  have hv(u:B)(p:u∈T.steps): implement ψ u w=w:=by unfold w; rw [map_sub,map_smul,a u p]; rw [T.fixed_Ω]; exact p -- order
  have hm: inner ℂ ω w=0:=by unfold w; rw [inner_sub_right,inner_smul_right, show inner ℂ ω ω=(1:ℂ) from by rw [inner_self_eq_norm_sq_to_K,T.unit_Ω]; simp,mul_one]; exact sub_self _
  have hb: DenseRange (vectorForm ψ ∘ x):= (frequency ψ).comp q (vectorForm ψ).continuous
  refine ⟨c, sub_eq_zero.mp (hb.eq_zero_of_inner_right ℂ (x:=w) fun i=> ?_)⟩ -- binders lean
  let b:= x i; let B':=vectorForm ψ b; let z:= ‖inner ℂ B' w‖
  choose F hF using Xv i
  have hi(j:ℕ): z^2≤e j*‖w‖^2:=by
    let p:=(F j); let v:= vectorForm ψ (b-p.val) - ψ (b-p.val) • ω
    have hz : inner ℂ v w=inner ℂ B' w:=by
      unfold v; rw [inner_sub_left,inner_smul_left,hm,mul_zero,map_sub,inner_sub_left,T.plays X w hv p,sub_zero,sub_zero] -- tune
    have hf:= hF j; rw [← T.evaluate_price] at hf; have he : ‖v‖^2<e j := hf
    have hg : z ≤ ‖v‖*‖w‖ := by unfold z; rw [←hz]; exact norm_inner_le_norm ..
    calc z^2 ≤ (‖v‖*‖w‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
         _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right he.le (sq_nonneg _)
  have ha : z^2≤0*‖w‖^2:= ge_of_tendsto (ht.mul_const _) (Eventually.of_forall hi)
  have hy:0≤z:= norm_nonneg _
  change inner ℂ B' w = _
  exact norm_eq_zero.mp (show z=0 from by nlinarith)
end Transaction
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.Theory.Transaction.generically
