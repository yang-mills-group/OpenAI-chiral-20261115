import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Bounded measurements over a blob with compact image
Topology on input tests not needed beyond representing bounded measurements
as `→ᵇ`-s (even the discrete topology suffices). -/
set_option autoImplicit false
noncomputable section
namespace YM.SU5.FiniteGaugeData.LocalLimit
-- used below on each test bank
open Function Filter Metric
open scoped Topology Classical BoundedContinuousFunction
variable {α γ D:Type}[TopologicalSpace α][NormedAddCommGroup γ][ProperSpace γ][PseudoMetricSpace D]
lemma measurements_compact (C d:ℝ)(hc:0<C)(T:α→ D)(he:IsCompact (closure (Set.range T))) :
    IsCompact (closure ({f:α →ᵇ γ | ‖f‖≤d ∧ ∀ i j, dist (f i) (f j) ≤ C*dist (T i) (T j)} : Set (α →ᵇ γ))):=by
 let S:= {f:α →ᵇ γ | ‖f‖≤d ∧ ∀ i j, dist (f i) (f j) ≤ C*dist (T i) (T j)}; change IsCompact (closure S)
 have hst(f:α →ᵇ γ)(u:f∈S) : ‖f‖≤d ∧ ∀ i j, dist (f i) (f j) ≤ C*dist (T i) (T j):=u
 refine TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure ?_) isClosed_closure
 refine totallyBounded_of_finite_discretization fun ε v=>?_
 let z:= ε/8; have hz:0<z:=by unfold z; positivity
 obtain ⟨Y,py,y,hy⟩:= exists_finite_cover_balls_of_isCompact_closure he (div_pos hz hc)
 obtain ⟨G,_,U,g⟩:= finite_cover_balls_of_compact (isCompact_closedBall (0:γ) d) hz
 letI:= y.fintype; letI:= U.fintype
 choose k hk using fun i : Y=> show ∃ v:α,T v=i.val from py i.property
 choose Dp hd using fun x: closedBall (0:γ) d=> show ∃ t:G,dist x.val t.val< z from (by obtain ⟨y,p,e⟩:= Set.mem_iUnion₂.mp (g x.property); exact ⟨⟨y,p⟩,e⟩)
 let F(f:↥S)(i: ↥Y):= (⟨f.val (k i), by rw [Metric.mem_closedBall,dist_zero_right]; exact (f.val.norm_coe_le_norm _).trans (hst _ f.property).1⟩ : closedBall (0:γ) d) -- d shadow ren
 refine ⟨Y→ G,inferInstance,fun i=> Dp ∘ F i,fun x y h=>?_⟩
 refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (C:=5*z) (by positivity)).2 fun i=> ?_) (by unfold z; linarith)
 obtain ⟨p,q,u⟩ := Set.mem_iUnion₂.mp (hy (Set.mem_range_self i)); let X: ↥Y:=⟨p,q⟩; let K:=k X
 have he(a: ↥S): dist (a.val i) (a.val K) ≤ z:= by
    apply ((hst _ a.property).2 ..).trans
    rw [show T K=p from hk X, mul_comm]; exact (le_div_iff₀ hc).1 (Metric.mem_ball.mp u).le
 have hx:Dp (F x X)= Dp (F y X):= congrFun h X
 have ht:dist (x.val K) (y.val K) ≤ 2*z:= by
    have ht:= hd (F x X); have hv:= hd (F y X); rw [hx] at ht; let d:= (Dp (F y X)).val
    change dist (x.val K) d < z at ht; change dist (y.val K) d < z at hv; linarith [dist_triangle_right (x.val K) (y.val K) d]
 linarith [dist_triangle4_right (x.val i) (y.val i) (x.val K) (y.val K), he x, he y] -- check order
end YM.SU5.FiniteGaugeData.LocalLimit
