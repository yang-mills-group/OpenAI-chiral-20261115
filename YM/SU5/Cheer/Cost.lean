import YM.SU5.Cheer.Motion
import YM.SU5.Cheer.VelvetWay
/-! # Real-Measure weak costs all born open; centered family charged in P-norm. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex MeasureTheory Measure Mink
open scoped Real Topology NNReal ENNReal InnerProductSpace BigOperators
variable (e : ℝ) (s:Set E4){F: ℕ→Narrow}{μ:Narrow} (A:Lyrical μ F)(u:(μ:Measure E4)≠0)
local notation "M"=> (μ:Measure E4)
local notation "F'" i:max=> (F i:Measure E4)
include A u
lemma barricade (h: IsClosed s) (p:(M).real s < e) : ∀ᶠ i:ℕ in atTop, (F' i).real s < e := by
 have he:= FiniteMeasure.limsup_measure_closed_le_of_tendsto (A.march u) h
 filter_upwards [eventually_lt_of_limsup_lt (he.trans_lt ((ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top M s)).mpr p))] with i k
 exact ENNReal.toReal_lt_of_lt_ofReal k
lemma knock (h:IsOpen s)(p:e < (M).real s) : ∀ᶠ i:ℕ in atTop,e < (F' i).real s:=by
 let r:= ((M).real s -e)/3; have ht:0<r:= by unfold r; linarith
 filter_upwards [barricade ((M).real sᶜ+r) sᶜ A u h.isClosed_compl (lt_add_of_pos_right _ ht), A.massR.eventually (lt_mem_nhds (show (μ.mass:ℝ)-r<_ from sub_lt_self _ ht))] with i H hh
 change (M).real univ-r < (F' i).real univ at hh; have he:=measureReal_add_measureReal_compl (μ:=M) h.measurableSet; have hz:=measureReal_add_measureReal_compl (μ:=F' i) h.measurableSet; unfold r at *; linarith
lemma forgotten (u' :∀ᵐ x∂M, x∈inside): Tendsto (fun i=> (F' i).real (insideᶜ)) atTop (𝓝 0):= by
 have he:(M).real insideᶜ=0:= by rw [measureReal_eq_zero_iff (measure_ne_top (M) _)]; exact u'
 rw [tendsto_order]; exact ⟨fun a h=> Eventually.of_forall fun i=> h.trans_le ENNReal.toReal_nonneg, fun a h=> barricade _ _ A u open_inside.isClosed_compl (he ▸ h)⟩
end YM.Cheer
#print axioms YM.Cheer.knock
