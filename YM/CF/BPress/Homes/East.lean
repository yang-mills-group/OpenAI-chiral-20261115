import YM.CF.BPress.Scale
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-!
 Supplement to the B-phase construction. Borel pricing domains (global version).
 `allHours` checks differentiable graph with its prescribed derivative
 *including* at endpoints (Hook paths live on a larger interval for the two jet tests).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Homes
open Real Filter Metric Set MeasureTheory Function
open scoped Topology BigOperators Classical
variable {X E : Type*}[TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {f g:X→ℝ→E}

private abbrev token (i : ℕ) := (i:ℝ)⁻¹
private lemma accept (F : ℝ→ E)(q : E)(x:ℝ) : HasDerivAt F q x ↔ ∀ n:ℕ, 0<n → ∃ m:ℕ, 0<m ∧ ∀ y∈Metric.ball x (token m), ‖F y-F x-(y-x) • q‖≤ token n*‖y-x‖:=by
 rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]; constructor
 · intro h n p
   obtain ⟨r,t,b⟩:= Metric.mem_nhds_iff.mp (h (by unfold token; positivity : 0< token n))
   obtain ⟨i,v,hx⟩:= Real.exists_nat_pos_inv_lt t
   exact ⟨i,v,(fun y h=>b (lt_trans h hx))⟩
 intro h r v; obtain ⟨n,t,b⟩:= Real.exists_nat_pos_inv_lt v; obtain ⟨m,u,p⟩:=h n t; filter_upwards [Metric.ball_mem_nhds x (by unfold token; positivity : 0<token m)] with j h
 exact (p j h).trans (mul_le_mul_of_nonneg_right b.le (norm_nonneg _))
lemma token_borel (c : ℝ)(p: Continuous f.uncurry)(v:Continuous g.uncurry): MeasurableSet {x| HasDerivAt (f x) (g x c) c}:=by
 simp_rw [accept, setOf_forall, setOf_exists,setOf_and]; apply MeasurableSet.iInter; intro i; apply MeasurableSet.iInter; intro _; apply MeasurableSet.iUnion; intro j; apply MeasurableSet.inter (MeasurableSet.const _); simp_rw [setOf_forall]; apply IsClosed.measurableSet; apply isClosed_iInter; intro y; apply isClosed_iInter; intro _; exact (isClosed_le (((p.uncurry_right y).sub (p.uncurry_right c)).sub ((v.uncurry_right c).const_smul _)|>.norm) continuous_const)

variable [CompleteSpace E] [FirstCountableTopology X]
private lemma FTC (f g:ℝ→E)(p:Continuous g): (∀ i∈Icc (0:ℝ) 2,HasDerivAt f (g i) i) ↔ (∀ i∈ Icc (0:ℝ) 2,(∫ x in (0:ℝ)..i,g x)=f i-f 0)∧HasDerivAt f (g 0) 0∧HasDerivAt f (g 2) 2:=by
 constructor
 · refine fun h=> ⟨fun i v=> ?_, h 0 (by norm_num), h 2 (by norm_num)⟩
   rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]; · intro x t; rw [uIcc_of_le v.1] at t; exact h x ⟨t.1,t.2.trans v.2⟩
   exact p.intervalIntegrable ..
 rintro ⟨H,T,V⟩ x ⟨l,r⟩; rcases eq_or_lt_of_le l with h|h; · subst x; exact T
 rcases eq_or_lt_of_le r with f0|f0; · subst x; exact V
 have t: HasDerivAt (fun i=> (∫ x in (0:ℝ)..i,g x)+ f 0) (g x) x:= (intervalIntegral.integral_hasDerivAt_right (p.intervalIntegrable ..) p.aestronglyMeasurable.stronglyMeasurableAtFilter p.continuousAt).add_const _
 apply t.congr_of_eventuallyEq; filter_upwards [Icc_mem_nhds h f0] with i w; rw [H i w,sub_add_cancel]
lemma allHours (p : Continuous f.uncurry)(q:Continuous g.uncurry): MeasurableSet {x|∀ j∈ Icc (0:ℝ) 2, HasDerivAt (f x) (g x j) j}:=by
 simp_rw [FTC (f _ ) (g _) (q.uncurry_left _), setOf_and,setOf_forall]; refine MeasurableSet.inter ?_ ((token_borel 0 p q).inter (token_borel 2 p q))
 exact (isClosed_iInter (fun i=> isClosed_iInter (fun _=> isClosed_eq (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' q 0 i) ((p.uncurry_right i).sub (p.uncurry_right _))))).measurableSet -- tune syntax. uncurry_right name
end YM.CF.BPress.Homes
