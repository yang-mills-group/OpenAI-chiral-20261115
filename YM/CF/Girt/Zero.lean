/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Rill.Sot
import YM.CF.Hive.Hen
import YM.Push.SECTOR_MEASURE.Presented
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
variable {f n :Side}{CΛ δ v a P h d μ ε w e:ℝ}
open Work.F05
private lemma maskgi (Y : Support f) (g : Config G₀ f → ℝ) (u : GaugeInvariant g) (x : ℝ) :
    GaugeInvariant (masked x Y g) := by
  intro t V
  unfold masked
  simp only [Set.indicator, Set.mem_setOf_eq, Healthy,gauge_flags,u t V]; congr!
lemma thumb (R : GramM n) (q : R.path.Bounds R.funds μ δ v) (V : Pane n) (t: Seat n→ SU.E) : R.path.inChannels R.funds R.p R.beta (gauge t V)=R.path.inChannels R.funds R.p R.beta V:=by
  have hm {k} (h : ℕ → Atom G₀ k) (m : ∀ i, (h i).Invariant) (x : Seat n) (t : Seat n → E) (U : Pane n) : PathData.atomSeries h R.p (gauge t U) x = PathData.atomSeries h R.p U x := by
    apply tsum_congr
    intro i
    refine maskgi ((h i).footprint x) _ ?_ _ t U
    intro t U; unfold Atom.unmasked; simp_rw [slot_gauge]; exact m i ..
  have hp (U : Pane n) (s : Seat n→ E) (i : Cell (More n)) : R.path.baseTerm R.funds R.p (gauge s U) i = R.path.baseTerm R.funds R.p U i := by
    simp only [PathData.baseTerm, PathData.kept, face_gauge, Gauge.chord_conj,ell_gauge q,Gauge.norm_adjoint]
    congr!
  simp only [PathData.inChannels, PathData.principal, pull_gauge_zero,hp, hm R.path.cubic (fun i => (q.invariant i).2.1), hm R.path.quartic (fun i => (q.invariant i).2.2),hm R.path.loop (fun i => (q.invariant i).1)]
-- gauge transformation at EVERY U, though not necessarily every mask's domain
structure Ward (R : GramM n) :Prop where
 area : ∃ a b c,R.path.Bounds R.funds a b c
 f : ∀ (s:Hub n), ∃ a v,PressB R.p s (R.F s) a v
 g : ∀ (s:Hub n),∃ a v,PressB R.p s (R.slip s) a v
 k : ∀ (i:Force n),∃ a v,ForceB R.p i (R.K i) a v

lemma traces (p:BudgetPoint) (F:RegBudget n) (v:∀ s: Hub n,∃ a y,PressB p s (F s) a y) (U:Pane n)(g:Seat n→ E): exponentL p F (gauge g U)=paintR false false (tradew _ g) (exponentL p F U):=by
 classical
 unfold exponentL; rw [map_sum]; refine sum_congr rfl fun i _=> ?_; obtain ⟨a,v,H⟩:=v i; unfold numbE; by_cases h: pingS p.threshold i.val.2 U; · rw [Set.indicator_of_mem (show gauge g U∈ _ from (pingB ..).2 h),Set.indicator_of_mem (show U∈ _ from h)]; exact H.gaugeV ..
 rw [Set.indicator_of_notMem (show gauge g U∉ _ from (mt (pingB ..).1 h)),Set.indicator_of_notMem (show U∉ _ from h),map_zero] -- tune
abbrev gird (g:Seat n→ E)(x:Orbit n): Orbit n:= (gauge g x.1,threadG g x.2)
lemma halt (p:BudgetPoint) (F:ForceBudget n)(v:∀ i:Force n,∃ a h,ForceB p i (F i) a h) (U:Orbit n)(g:Seat n→ E): fueled p F (gird g U)= paintR false false (tradew _ g) (fueled p F U):=by
 classical
 unfold fueled; rw [map_sum]; refine sum_congr rfl fun i _=> ?_; unfold coverF; by_cases k:(i.biUnion fun j=>j.val.2) = flags p.threshold U.1∧ Set.PairwiseDisjoint (i:Set (Force n)) (fun x=> x.val.1.val.2)
 · have hu:flags p.threshold (gird g U).1=flags p.threshold U.1:= gauge_flags ..; rw [if_pos (And.intro (k.1.trans hu.symm) k.2),if_pos k,map_prod]; refine prod_congr rfl fun j _=> ?_; obtain ⟨_,_,t⟩:= v j
   unfold clamp boundF; by_cases h: pingS p.threshold (j.val.1.val.2 \ j.val.2) U.1
   · rw [if_pos ((pingB U.1 g).2 h),if_pos h]; exact t.gaugeV ..
   rw [if_neg (mt (pingB U.1 g).1 h),if_neg h,map_zero]
 rw [if_neg (fun e=>k ⟨e.1.trans (gauge_flags _ _ _),e.2⟩),if_neg k,map_zero]
lemma spinM (U:UNI (Single n)): Continuous (paintR false false U):=(paintR false false U).toLinearMap.continuous_of_finiteDimensional
lemma march (R:GramM n)(H:Ward R)(x:Orbit n)(g:Seat n→ E): R.board (gird g x)= paintR false false (tradew n g) (R.board x):=by
 letI : NormedAlgebra ℚ (Scree.Cipher n) := NormedAlgebra.restrictScalars ℚ ℝ (Scree.Cipher n)
 unfold GramM.board; rw [traces _ _ H.f, traces _ _ H.g, halt _ _ H.k,←map_add,map_mul,map_exp _ (spinM (n:=n) _)]
end YM.CF.Girt
