import YM.CF.DPress.Chess.Floor.Porch
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ContinuousMapDense
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
namespace Porch
variable {X Z:Type*}[TopologicalSpace X][MeasurableSpace X][NormalSpace X][BorelSpace X][NormedAddCommGroup Z][NormedSpace ℝ Z][MeasurableSpace Z][BorelSpace Z][SecondCountableTopology Z]{u:ℝ} (μ:Measure X) [IsProbabilityMeasure μ] [μ.WeaklyRegular]
-- choose approximants subsequence & truncate for point bounds and sector closure, thus L1 and AE convergence.
def halt (u:ℝ) (x:Z) := (u/max ‖x‖ u) • x
lemma halt_C (v:0<u): Continuous (halt u (Z:=Z)):=by unfold halt; exact (continuous_const.div (continuous_norm.max continuous_const) (fun i=>(lt_of_lt_of_le v (le_max_right ..)).ne')).smul continuous_id
lemma halt_u(v:0<u)(x:Z): ‖halt u x‖ ≤ u:=by unfold halt; rw [norm_smul,Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,div_le_iff₀ (lt_of_lt_of_le v (le_max_right ..))]; exact mul_le_mul_of_nonneg_left (le_max_left ..) v.le
lemma halt_right(v:0<u)(x:Z)(p:‖x‖≤u):halt u x=x:=by rw [halt,max_eq_right p,div_self v.ne',one_smul]
lemma tend (F:X→Z)(p:Measurable F)(u':0<u)(h:∀ i,‖F i‖≤u):∃ G:ℕ→X→Z,(∀ i,Continuous (G i)) ∧ (∀ i x,‖G i x‖≤u) ∧∀ᵐ x∂μ,Tendsto (fun i=>G i x) atTop (𝓝 (F x)):=by
 let v: MemLp F 1 μ:=MemLp.of_bound p.aestronglyMeasurable u (Eventually.of_forall h); let k(n:ℕ):ℝ:=1/((n:ℝ)+1); have he:Tendsto (fun i=> ENNReal.ofReal (k i)) atTop (𝓝 0):=by rw [←ENNReal.ofReal_zero]; exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
 have hg(n:ℕ):0< k n:=by unfold k; positivity
 choose y a p using fun i:ℕ=> MemLp.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top v (ne_of_gt (ENNReal.ofReal_pos.mpr (hg i)))
 have ht:Tendsto (fun i=> eLpNorm ((y i:X→Z)-F) 1 μ) atTop (𝓝 0):=tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun i=> bot_le) (fun i=> (eLpNorm_sub_comm ..).trans_le (a i))
 obtain ⟨ℓ,f,v⟩:= (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun i=>(p i).1) v.1 ht).exists_seq_tendsto_ae; let g(i:ℕ):X→Z:= halt u ∘ y (ℓ i); refine ⟨g,fun i=> (halt_C u').comp (y _).continuous,fun i x=>halt_u u' _, v.mono fun i x=>?_⟩; exact (halt_right u' (F i) (h i)) ▸ ((halt_C u').tendsto (F i)).comp x -- tune ▸ may cast inside 
end Porch
end YM.CF.DPress.Chess
