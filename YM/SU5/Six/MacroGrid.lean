import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace YM.MacroGrid
open Function Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal Classical BigOperators

/-!
# Full-tick quadrature

Global Vantage measure is Lebesgue in pose coordinates (fermion
lattice units for the physical gauges). The sum at t will be literal
finite smooth-test quadrature at mesh h with payment h^4. Here are
some tools using floor boxes (no continuity on unsmoothed pose kernels
will be inserted implicitly).
-/
variable {I:Type}[Fintype I]
local notation "R" => I→ℝ
local notation "Λ" => I→ℤ
local notation "µ"=> (volume : Measure (R))
def atTick (h:ℝ)(k:Λ)(j:I):ℝ:= k j*h
-- sed: coerces via h
lemma tick_add(h:ℝ)(k p:Λ): atTick h (k+p)=atTick h k + atTick h p:= by funext; simp only [atTick,Pi.add_apply,Int.cast_add,add_mul]
def floorTicks (h:ℝ)(x:R)(j:I):ℤ := ⌊x j/h⌋
def gridRoom (h:ℝ)(k:Λ):Set (R):= Set.univ.pi (fun j=>Set.Ico (atTick h k j) (atTick h k j+h))
def floorCost {E:Type} (h:ℝ)(f:(I→ℤ)→ E)(x:I→ℝ) := f (floorTicks h x)
variable (h:ℝ)(u:0<h)(k:I→ℤ)(x:I→ℝ)
include u
lemma room_iff : x∈gridRoom h k ↔ floorTicks h x = k := by
 simp only [gridRoom,atTick,Set.pi,Set.mem_setOf_eq,Set.mem_univ,forall_true_left,Set.mem_Ico,funext_iff,floorTicks,Int.floor_eq_iff]
 apply forall_congr'; intro j; rw [le_div_iff₀ u,div_lt_iff₀ u]; ring_nf
lemma occurrence (j:I) : atTick h (floorTicks h x) j ≤ x j ∧ x j < atTick h (floorTicks h x) j+h:= (room_iff h u (floorTicks h x) x).2 rfl j (Set.mem_univ j)
lemma rounds_close : dist (atTick h (floorTicks h x)) x < h := by
 refine (dist_pi_lt_iff u).2 (fun i=>?_)
 obtain ⟨a,b⟩:= occurrence h u x i
 rw [Real.dist_eq]; apply abs_lt.mpr; constructor<;>linarith
lemma box_area : µ (gridRoom h k)=(ENNReal.ofReal h)^Fintype.card I:= by unfold gridRoom; rw [volume_pi_pi]; simp
lemma block_payment : µ.real (gridRoom h k)=h^Fintype.card I:= by rw [measureReal_def,box_area h u,ENNReal.toReal_pow,ENNReal.toReal_ofReal u.le]
omit u in
lemma room_admitted : MeasurableSet (gridRoom h k):= MeasurableSet.univ_pi (fun _=>measurableSet_Ico)
lemma finite_ledger (S:Set (R))(p:IsCompact S): Set.Finite {k:I→ℤ|atTick h k ∈S}:= by
 obtain ⟨C,c,F⟩:= p.isBounded.exists_pos_norm_le
 let a:Λ:=fun _=> ⌊-C/h⌋; let b:Λ:=fun _=>⌈C/h⌉
 refine (Set.Finite.pi fun (i:I)=> Set.finite_Icc (a i) (b i)).subset (fun k (t: atTick h k ∈ S)=>?_)
 -- note predicate {f|∀ i,f i∈...}
 have he:= (pi_norm_le_iff_of_nonneg c.le).1 (F _ t)
 have ht(j:I): -(C/h) ≤ (k j:ℝ)∧ (k j:ℝ) ≤ C/h:= by
   specialize he j; rw [Real.norm_eq_abs] at he
   rw [le_div_iff₀ u] -- second
   refine ⟨?_,(abs_le.mp he).2⟩
   rw [←neg_div,div_le_iff₀ u]; exact (abs_le.mp he).1
 intro i _
 have hx:= ht i
 have hp: -C/h ≤ (k i:ℝ):=(neg_div ..).le.trans hx.1
 exact ⟨(Int.floor_le_floor hp).trans (le_of_eq (Int.floor_intCast _)),(Int.ceil_intCast _|>.symm.le).trans (Int.ceil_le_ceil hx.2)⟩
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
lemma room_price (G:(Λ)→E) (L:Finset (Λ))(v: ∀ k,k∉L→G k=0):
 Integrable (floorCost h G) µ ∧ ∫ x,floorCost h G x= h^Fintype.card I • ∑ i∈L,G i:= by
 let F (i:Λ) := (gridRoom h i).indicator (fun _=> G i)
 have ht : floorCost h G= fun x=> ∑ i∈L,F i x := by
    funext x; let i:=floorTicks h x
    rw [Finset.sum_eq_single i]
    · unfold F; rw [Set.indicator_of_mem ((room_iff h u i x).2 rfl)]; rfl
    · intro j _ p; exact Set.indicator_of_notMem (fun g=>p ((room_iff h u j x).1 g|>.symm)) _
    intro e; unfold F; rw [v i e,Set.indicator_of_mem ((room_iff h u i x).2 rfl)]
 have hx(i:Λ): Integrable (F i) µ:= (integrable_indicator_iff (room_admitted h i)).2 (integrableOn_const (by rw [box_area h u]; finiteness))
 rw [ht]
 refine ⟨integrable_finsetSum _ (fun i _=> hx i),?_⟩
 rw [integral_finsetSum _ (fun i _=>hx i), Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; unfold F; rw [integral_indicator_const _ (room_admitted h i), block_payment h u]
lemma floors_integrable (G:(Λ)→E) (v:(Function.support G).Finite): Integrable (floorCost h G) µ := (room_price h u G v.toFinset (fun i p=> by_contra fun n=> p (v.mem_toFinset.mpr n))).1
lemma floors_pullback (g:(R)→E) (b:HasCompactSupport g): Integrable (fun x:R=>g (atTick h (floorTicks h x))) µ := floors_integrable h u (g ∘ atTick h) ((finite_ledger h u (tsupport g) b).subset (fun i h=>subset_closure (show g _≠0 from h)))
omit u
lemma rSum_limit (δ:ℕ→ℝ) (p:Tendsto δ atTop (𝓝 0))(g:(R)→E) (s:Continuous g)(u:∀ i,0<δ i)(b:HasCompactSupport g) : Tendsto (fun i=> ∫ x:I→ℝ, g (atTick (δ i) (floorTicks (δ i) x))) atTop (𝓝 (∫ x,g x)):= by
 obtain ⟨C,c,V⟩:=b.exists_pos_le_norm
 obtain ⟨D,Y⟩:= s.bounded_above_of_compact_support b
 let X:=Metric.closedBall (0:I→ℝ) (C+1)
 let A:=X.indicator (fun _=>D)
 have he:0≤ D := (norm_nonneg _).trans (Y (fun _=>0))
 refine tendsto_integral_filter_of_dominated_convergence A (Eventually.of_forall fun i=> (floors_pullback (δ i) (u i) g b).aestronglyMeasurable) ?_ ?_ ?_
 · filter_upwards [p.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with i t
   apply ae_of_all
   intro x
   by_cases q:x∈X
   · exact le_trans (Y _) (Set.indicator_of_mem q (fun _=> D)).symm.le
   rw [show A x=0 from Set.indicator_of_notMem q _]
   let y:= atTick (δ i) (floorTicks (δ i) x)
   have ht : g y=0:= V y (by
     have h:C+1< ‖x‖:=by simpa [X,Metric.mem_closedBall,dist_zero_right] using q
     have hv:dist x y<1:=by rw [dist_comm]; exact (rounds_close _ (u i) x).trans t
     have hu:= dist_triangle x y 0; rw [dist_zero_right,dist_zero_right] at hu; linarith)
   change ‖g y‖≤0; rw [ht,norm_zero]
 · exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 (integrableOn_const (isCompact_closedBall .. |>.measure_ne_top))
 apply ae_of_all
 intro x
 refine (s.tendsto x).comp ((show Tendsto (fun i=> atTick (δ i) (floorTicks (δ i) x)) atTop (𝓝 x) from Metric.tendsto_nhds.mpr (fun ε t=>?_)))
 filter_upwards [p.eventually (gt_mem_nhds t)] with i u'; exact (rounds_close _ (u i) x).trans u'
end
end YM.MacroGrid
