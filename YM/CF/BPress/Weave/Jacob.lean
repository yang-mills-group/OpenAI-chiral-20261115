import YM.CF.BPress.Weave.Van
import YM.CF.BPress.Census
/-! eq:B-jcost & local assignment. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Branch Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s: Side}{B:BandWidth}(X : Bands s B)
abbrev Tender := Seal X.Hcols→ℝ
def geoBill (D:ℕ)(a k:ℝ):= (k* n_ang D)*harm 3 (a/2) 4
def priceFen (C: Seal X.Hcols → Toll (Axon X)): Tender X:=fun S=>∑ i,C S i i
lemma pay_grid (C:Seal X.Hcols → Toll (Axon X)){a k:ℝ}(v:0<a)(L:Branch.Ledger a C k)(A:Seal X.Hcols→Collected X.Hcols (Axon X))(p:∀ i,Currency (soils X) i (C i) (A i)): Ledger.Cash id (priceFen X C) (a/2) (geoBill B.D a k):=by
 let K:= priceFen X C; have hk(i):0≤K i:= sum_nonneg (fun l _=>(p i).nonn l l); have he:=L.posP; refine ⟨hk,fun u=>?_ ⟩; let k':=k*(n_ang B.D); let P(m:ℕ):=(4*(m:ℝ)+1)^3* Real.exp (-(a/2)*m); let Q:= Ledger.score id K (a/2) u; have hQ(i):0≤Q i:= by unfold Q Ledger.score; split; exact mul_nonneg (Real.exp_pos _).le (hk _); rfl
 apply budget_fiberwise Finset.card hQ _ (budget_scale (show 0≤ k' by unfold k'; positivity) (thin_count 3 (a/2) 4 (half_pos v) (by norm_num))); intro m S U; let T:= columnBall X u m; let W:=coverPrice X T; let R:= Real.exp (-(a/2)*m); have hr:= (Real.exp_pos (-(a/2)*m)).le; let Y:= S.filter fun z=> u∈ z; let f(z i):=rent a z*C z i i; have ht(i:Axon X):∑ z∈Y, f z i ≤ k:=by apply le_trans _ ((single_le_sum (f:=saleM a C i) (fun j _=> sale_nn (fun j=> (p j).nonn) a i j) (mem_univ i)).trans (L.rows i)); exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>mul_nonneg (rent_pos a j).le ((p j).nonn i i)) -- tune
 calc ∑ z∈S,Q z ≤ ∑ z∈Y, R* ∑ i∈W, f z i:= Eq.le ?_
      _ = R*∑ i∈W,∑ z∈Y,f z i:=by rw [←mul_sum,sum_comm]
      _ ≤ R * (W.card*k) := mul_le_mul_of_nonneg_left ((sum_le_sum (fun i _=>ht i)).trans_eq (by rw [sum_const,nsmul_eq_mul])) hr
      _ ≤ _ := ?_
 · unfold Q Ledger.score K priceFen; rw [← sum_filter]; apply sum_congr rfl; intro z b; obtain ⟨b,x⟩:= mem_filter.mp b; unfold f; rw [mul_sum]; simp_rw [mul_sum]; unfold rent R; simp only [id_eq,U z b]; simp_rw [←mul_assoc,←Real.exp_add, show -(a/2)*↑m + a*↑m=a/2*↑m by ring]; refine (sum_subset (subset_univ W) (fun i _ n=>?_ )).symm; apply mul_eq_zero_of_right; by_contra h; obtain ⟨q,g,_⟩:= (p z).trunk i i h; apply n; refine mem_filter.mpr ⟨mem_univ _,?_⟩; exact column_mono X u (U z b|>.le) (turf_lim X z q u x (show zSite X i∈ z from g)) -- tune `sum_subset` direction
 · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show W.card≤ n_ang B.D* (4*m+1)^3 from (cover_count X T).le.trans (Nat.mul_le_mul_left _ (cost_bay X u m)))) he) hr).trans_eq ?_; unfold k'; push_cast; ring
-- Jacob data
variable {F:Fare X}
structure JacData (F:Fare X)(l:  Seal X.Hcols → Tender X)(b:Tender X)(a k:ℝ):Prop where
 turf S : b S≠0→ Turf X S
 budget : Ledger.Cash id b a k
 value S T : |l S T| ≤ b S
 localz S : Zoned S (l S)
 ebb S : l S ∅=0
 audit T : jacdiff X F T=∑ S, l S T
namespace Summer
variable {X}{u l:ℝ}{r k:ℕ}(p:Summer X F u l r k)
include p
lemma j_cost : ∃ A b, JacData X F A b (grassRate (k*r)/2) (2*geoBill B.D (grassRate (k*r)) (grainSelect B.D r k)):=by
 obtain ⟨T,C,b,H,h⟩:= p.slow; let M(i j):=Matrix.trace (T i j); let u(i):= priceFen X C i; have hu(i j) : |M i j|≤ u i:= (abs_sum_le_sum_abs ..).trans (sum_le_sum fun v _=> (b i).pay v v j); refine ⟨fun i j=> M i ∅-M i j,_,fun S v=>?_ ,(pay_grid X C (gr_pos (k*r)) H T b).scale 2 (by norm_num),fun i j=>?_,fun S A B u=> ?_,by simp,fun j=>?_⟩ -- tune
 · obtain ⟨i,_,p⟩:= exists_ne_zero_of_sum_ne_zero (show u S≠0 from right_ne_zero_of_mul v); exact ((b S).trunk i i p).1
 · exact (abs_sub (M i ∅) (M i j)).trans (by linarith only [hu i ∅,hu i j]) -- tune
 · exact congrArg (fun x=> M S ∅-x) (sum_congr rfl (fun i _=> (b S).sees i i A B u)) -- tune
 rw [jacdiff,p.root_eq,p.root_eq,sum_sub_distrib]; unfold traceM; simp only at h; rw [h,h]; simp only [Matrix.trace_sum]; unfold M; ring
end Summer
end YM.CF.BPress.Weave
