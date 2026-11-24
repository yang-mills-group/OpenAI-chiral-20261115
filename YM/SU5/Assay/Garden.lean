import YM.SU5.Assay.GridMass
import YM.SU5.Assay.Ripen
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
open TopologicalSpace
/-! Compact-album bound consistent even at uncontrolled early pose stages. -/
lemma fertilizer (K:Compacts Vantage):∃F:SampleDose,∀y∈(K:Set Vantage),F.val y=1:=by
 obtain ⟨d,n,p⟩:=K.isCompact.isBounded.exists_pos_norm_le
 let r:ContDiffBump (0:Vantage) := ⟨_,_,n,lt_add_one d⟩
 exact ⟨⟨_,r.contDiff,r.hasCompactSupport⟩,fun _ t=>r.one_of_mem_closedBall
  (by rw [Metric.mem_closedBall,dist_zero_right]; exact p _ t)⟩
variable (P:Spine)
-- inequality comparing different paid grid sets
lemma grid_control {F G:SampleDose} (h:∀y∈tsupport F.val,G.val y=1) (t:ℕ){M:ℝ}
 (n:0≤M)(p:∀y,‖F.val y‖≤M):P.gridMass F t≤P.gridMass G t*M:=by
 have u:=P.macroStep_pos t
 have q(i:Cover)(v:i∈P.usedGrid t F):G.val (P.meshPose t i)=1:=h _ ((P.usedPose t F i).mp v)
 have t':P.usedGrid t F ⊆ P.usedGrid t G:=by
   intro i v; exact (P.usedPose t G i).mpr (subset_closure (show G.val (P.meshPose t i) ≠ 0 from (q i v).symm ▸ one_ne_zero))
 unfold gridMass
 rw [sum_mul]
 refine sum_le_sum_of_subset_of_nonneg t' ?_ |>.trans' ?_
 · exact fun i _ _=>mul_nonneg (norm_nonneg (P.activation t G i)) n
 · refine Finset.sum_le_sum fun i v=>?_
   rw [activation_norm,activation_norm,q i v,norm_one,mul_one]
   exact mul_le_mul_of_nonneg_left (p _) (pow_nonneg u.le _)
lemma grain_price (K:Compacts Vantage):∃ c:ℝ,0≤c∧∀ F:SampleDose,tsupport F.val ⊆ K → ∀M:ℝ,0≤M →
 (∀y,‖F.val y‖≤M)→∀t,P.gridMass F t≤c*M:=by
 obtain ⟨G,h⟩:=fertilizer K
 obtain ⟨c,p⟩:=(P.gridMass_limit G).bddAbove_range
 refine ⟨max 0 c,le_max_left ..,fun F v M n q t=>
  (P.grid_control (F:=F) (G:=G) (fun y i=>h y (v i)) t n q).trans ?_⟩
 exact mul_le_mul_of_nonneg_right (le_trans (p (mem_range_self t)) (le_max_right 0 c)) n
-- And hence integral price on Vantage
include P in
lemma dose_price (K:Compacts Vantage):∃ c:ℝ,0≤c∧∀ F:SampleDose,tsupport F.val ⊆ K → ∀M:ℝ,0≤M →
 (∀y,‖F.val y‖≤M)→(∫y,‖F.val y‖)≤c*M:=by
 obtain ⟨c,p,t⟩:=P.grain_price K
 exact ⟨c,p,fun F y M n h=> le_of_tendsto' (P.gridMass_limit F) (t _ y M n h)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
