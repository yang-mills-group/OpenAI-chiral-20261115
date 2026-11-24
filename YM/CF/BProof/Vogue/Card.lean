import YM.CF.Skye.Zap
/-! Uniform finite distributors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter Metric Set MeasureTheory Skye Equiv
open scoped Topology BigOperators NNReal ENNReal Classical
variable {I X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]
section
variable [Fintype X][MeasurableSingletonClass X]
@[simp] lemma postcard(x:X) : paperMeas X {x}= (Fintype.card X : ℝ≥0∞)⁻¹ := by simp [paperMeas]
variable (X) [Nonempty X]
lemma credit (μ:Measure X) [IsProbabilityMeasure μ] (h:∀ i j:X, μ {i}=μ {j}) : μ=paperMeas X:=by
 refine (ext_iff_measureReal_singleton.mpr ?_); intro x
 have ht (ν:Measure X) [IsProbabilityMeasure ν] (h:∀ i,ν {i}=ν {x}) : (Fintype.card X:ℝ)*(ν.real {x})=1:= calc
    _ = ∑ i:X, ν.real {i}:=by apply Eq.trans _ (Finset.sum_congr rfl (f:=fun _=> ν.real {x}) (fun i _=> by unfold Measure.real; rw [h i])); simp
    _ = 1:=by simp
 exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne') ((ht μ (fun i=>h i x)).trans (ht (paperMeas X) (by simp)).symm) -- tune
variable {X}
lemma atomMP {μ:Measure Y}[IsProbabilityMeasure μ] (f:Y→X) (h:Measurable f)(p:∀ x y:X,∃ F:Y→ Y,MeasurePreserving F μ μ∧∀ i,f i=x ↔ f (F i)=y) : MeasurePreserving f μ (paperMeas X):=by
 haveI := Measure.isProbabilityMeasure_map (μ:=μ) h.aemeasurable -- tune implicit
 refine ⟨h,credit X (μ.map f) (fun i j=>?_)⟩; obtain ⟨F,e,p⟩:=p i j; rw [Measure.map_apply h (measurableSet_singleton i), Measure.map_apply h (measurableSet_singleton j),← e.measure_preimage (h (measurableSet_singleton j)).nullMeasurableSet]; exact congrArg μ (Set.ext p)
variable [Fintype Y][MeasurableSingletonClass Y][Nonempty Y]
lemma orderMP(e:X≃Y) : MeasurePreserving e (paperMeas X) (paperMeas Y) := by
 refine ⟨measurable_of_countable _,Measure.ext_of_singleton fun i=>?_⟩; rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),show (⇑e) ⁻¹' {i}={e.symm i} from by ext; simp [e.apply_eq_iff_eq_symm_apply],postcard,postcard,Fintype.card_congr e]
variable (X Y)
lemma parcelPair: paperMeas (X×Y)=(paperMeas X).prod (paperMeas Y):=Eq.symm (credit _ _ (fun ⟨a,b⟩ ⟨i,j⟩=> by rw [←singleton_prod_singleton,←singleton_prod_singleton]; simp only [Measure.prod_prod,postcard]))
lemma parcelPi (I:Type*)[Fintype I][DecidableEq I]: paperMeas (I→ X)=Measure.pi (fun _:I=> paperMeas X):= Eq.symm (credit _ _ (fun a b=> by rw [Measure.pi_singleton,Measure.pi_singleton]; simp)) -- decidable issue Classical
end
end YM.CF.BProof.Vogue
