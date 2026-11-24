import YM.CF.DPress.FD.Law.Sat
import Mathlib.Probability.Independence.Basic
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Filter MeasureTheory ProbabilityTheory Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {I X Y:Type*}[MeasurableSpace I][MeasurableSpace X][MeasurableSpace Y][Fintype I][MeasurableSingletonClass I]
namespace Cash
variable (T:Cash I)
def PM : Measure I:= ∑ i, ENNReal.ofReal (T.μ i) • Measure.dirac i
lemma pm_apply (S:Set I): T.PM S = ENNReal.ofReal (T.turn (·∈S)):=by
 unfold PM turn; simp only [Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply]; rw [ENNReal.ofReal_sum_of_nonneg (hf:=fun _ _=> T.nn _)]; rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun x _=> by by_cases h:x ∈ S <;> simp [*,smul_eq_mul]
instance PMprob : IsProbabilityMeasure T.PM:= ⟨by simp only [pm_apply, mem_univ,T.mint,ENNReal.ofReal_one]⟩
lemma pm_P (s:Equiv.Perm I)(p:Deck.Chooses T s): MeasurePreserving s T.PM T.PM:=by
 let h:= measurable_of_countable s; refine ⟨h,Measure.ext fun A v=>?_⟩; rw [Measure.map_apply h v,T.pm_apply,T.pm_apply]; apply congrArg _; unfold turn; rw [Finset.sum_filter, Finset.sum_filter]; conv_rhs=> rw [← Equiv.sum_comp s _]
 apply Finset.sum_congr rfl; intro i _; by_cases f:s i∈A <;> simp [p,f]
lemma indie {R S:Setoid I}(p:T.Pair R S){f:I→ X}{g:I→ Y}(v:Holds f R)(w:Holds g S): IndepFun f g T.PM:=by
 rw [indepFun_iff_measure_inter_preimage_eq_mul]; intro A B _ _; rw [pm_apply,pm_apply,pm_apply, T.tape (P:=fun i=> i∈ f ⁻¹' A ∩ g ⁻¹' B) (Q:=fun i=> (i∈ f ⁻¹' A)∧(i∈g ⁻¹' B)) (fun i=>Iff.rfl), T.region p _ _,ENNReal.ofReal_mul (T.size _)]; -- tune signature & order
 · intro i j u; change (f i∈A)=(f j∈A); rw [v i j u]
 · intro i j u; change (g i∈B)=(g j∈B); rw [w i j u]
end Cash
end YM.CF.DPress.FD
