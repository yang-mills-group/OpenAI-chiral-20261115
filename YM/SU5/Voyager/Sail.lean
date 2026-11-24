import YM.SU5.Voyager.Cinder
/-! # Mixing in a specified part of Hilbert space. Test along arbitrary filter. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup.Burst
open Filter Function Set Submodule Metric
open scoped InnerProductSpace Topology Classical
variable {I:Type*}{K:Type*}{H:Hilbert}(L:Filter K) (U:K→ H.Op)(P:I→H)
private lemma atClosed {M:Type*}[SeminormedAddCommGroup M] (F:K→ M→ℂ){c:ℝ}(hc:0≤c)
    (h : ∀ k u v,dist (F k u) (F k v) ≤ c*dist u v) : IsClosed {x:M| Tendsto (fun i=>F i x) L (𝓝 0)}:= by
 apply isClosed_of_closure_subset; intro x p; refine Metric.tendsto_nhds.mpr fun ε e=>?_; let r:=ε/(2*(c+1)); have hr:0<r:=by positivity
 obtain ⟨y,hy,hx⟩:= Metric.mem_closure_iff.mp p r hr; filter_upwards [ (show Tendsto (fun i=>F i y) L (𝓝 0) from hy).eventually (Metric.ball_mem_nhds (0:ℂ) (by positivity:0<ε/2))] with i v;  apply lt_of_le_of_lt (dist_triangle _ (F i y) _); have ht:=h i x y; have he:= mul_le_mul_of_nonneg_left hx.le hc; have hg : r*(2*(c+1))=ε:=div_mul_cancel₀ _ (by positivity); linarith

def fleeting : Submodule ℂ H where
 carrier:= {x:H|∀ y:H,Tendsto (fun k=>inner ℂ y (U k x)) L (𝓝 0)}
 zero_mem':= by intro y; simpa using (tendsto_const_nhds (x:=(0:ℂ)) (f:=L))
 add_mem' {x y} h p:=by intro z; simp_rw [map_add,inner_add_right]; exact add_zero (0:ℂ) ▸ Tendsto.add (h z) (p z)
 smul_mem' c x h:=by intro z; simp_rw [map_smul,inner_smul_right]; simpa only [mul_zero] using (h z).const_mul c
-- no uniformly over time here; used arbitrary L. Closed.
variable (h:∀ i, ‖U i‖≤1)
include h
lemma closedFleet : IsClosed ((fleeting L U) : Set H) := by
 rw [show ((fleeting L U): Set H) = ⋂ y:H, {x : H| Tendsto (fun i=>inner ℂ y (U i x)) L (𝓝 0)} from Set.ext fun x=> by rw [Set.mem_iInter]; rfl ]; refine isClosed_iInter (fun y=> atClosed L (fun i x : _=> inner ℂ y (U i x)) (norm_nonneg y) fun i x z=>?_)
 rw [dist_eq_norm, ← inner_sub_right,← map_sub,dist_eq_norm]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((U i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (h i))) (norm_nonneg _))
lemma payClosed (u:H)(p:Dense (span ℂ (Set.range P): Set H))(t:∀ i, Tendsto (fun k=> inner ℂ (P i) (U k u)) L (𝓝 0)): u∈ fleeting L U:=by
 intro x; let f:=fun k (y:H)=>inner ℂ y (U k u); let S : Set H := {y:H|Tendsto (fun i=> f i y) L (𝓝 0)} -- fix
 have hw:IsClosed S:=atClosed L f (norm_nonneg u) fun i y z=>by
    unfold f; rw [dist_eq_norm, ←inner_sub_left,dist_eq_norm,mul_comm]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((U i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (h i))) (norm_nonneg _))
 refine closure_minimal ?_ hw (p x); intro y e; refine Submodule.span_induction (s:=Set.range P) (p:=fun u _=>u∈S) ?_ ?_ ?_ ?_ e
 · rintro u ⟨i,rfl⟩; exact t i
 · change Tendsto (fun i=>inner ℂ 0 (U i u)) L (𝓝 0); simp; exact tendsto_const_nhds

 · intro a b p q w v; change Tendsto (fun i=>inner ℂ (a+b) (U i u)) L (𝓝 0); simp_rw [inner_add_left]; exact add_zero (0:ℂ) ▸ Tendsto.add (show Tendsto (fun i=>inner ℂ a (U i u)) L (𝓝 0) from w) (show Tendsto (fun i=>inner ℂ b (U i u)) L (𝓝 0) from v)
 · intro c a p v; change Tendsto (fun i=>inner ℂ (c • a) (U i u)) L (𝓝 0) -- clash
   simp_rw [inner_smul_left]; simpa only [mul_zero] using (show Tendsto (fun i=>inner ℂ a (U i u)) L (𝓝 0) from v).const_mul (starRingEnd _ c)
end YM.OS.Semigroup.Burst
