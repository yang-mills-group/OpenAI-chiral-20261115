import YM.CF.BPress.Weave.Aura
/-! summation & row sup. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Lattice Wilson Branch Finset RG Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {I Y: Type*}[Fintype I][Fintype Y][DecidableEq Y]{c:Centr Y I}
variable {a k:ℝ}
namespace Aura
-- slightly simpler than Branch.Flow: only request entrywise convergence.
def tPlot (A:ℕ→Collected Y I): Collected Y I:= fun S i j=> ∑' n:ℕ,A n S i j
lemma flow (F:ℕ→Collected Y I)(d:ℕ→ℝ)(p:∀ i,Aura c a (d i) (F i))(w:SumBudget d k)(h:0≤a): Aura c a k (tPlot F):=by
 choose G C l L e using p; have ht (x S i j) :=(l x S).nonn i j; have he S i j: Summable fun n=> C n S i j := (w.2.1).of_nonneg_of_le (fun n=>ht n S i j) (fun n=>(L n).price h (ht n) ..); let K (S:Seal Y)(i j:I):= ∑' n, C n S i j
 have hg(S T)(i j:I): Summable (fun n=> G n S T i j):= Summable.of_norm (he S i j|>.of_nonneg_of_le (fun n:ℕ=> norm_nonneg (G n S T i j)) (fun n=>(l n S).pay i j T)); have hs i j:Summable (fun n=>saleM a (C n) i j) := summable_sum fun S _=>(he S i j).mul_left _
 have H(i j:I) : saleM a K i j=∑' n,saleM a (C n) i j:=by unfold saleM K; rw [Summable.tsum_finsetSum (f:=fun S n=>rent a S * C n S i j) (fun S _=>(he S i j).mul_left _)]; simp_rw [tsum_mul_left]
 refine ⟨_,K,fun S=> Currency.flow _ _ (fun n=>l n S) (he S),⟨budget_nonneg w,?_,?_⟩,fun x=>?_⟩
 · intro i; simp_rw [H]; rw [← Summable.tsum_finsetSum (f:=fun j n=>saleM a (C n) i j) (fun j _=>hs i j)]; exact ((summable_sum (fun j (_:j∈ (univ:Finset I))=> hs i j)).tsum_le_tsum (fun n=>(L n).rows i) w.2.1).trans w.2.2
 · intro j; simp_rw [H]; rw [← Summable.tsum_finsetSum (f:=fun i n=>saleM a (C n) i j) (fun i _=>hs i j)]; exact ((summable_sum (fun i (_:i∈ (univ:Finset I))=> hs i j)).tsum_le_tsum (fun n=>(L n).cols j) w.2.1).trans w.2.2
 ext i j; simp only [tPlot,e,Matrix.sum_apply]; exact Summable.tsum_finsetSum (f:=fun S n=> G n S x i j) (fun S _=>hg S x i j)
def RowCap (F:Collected Y I)(C:ℝ) : Prop:= ∀ S i, ∑ j, |F S i j|≤ C
lemma cap {F:Collected Y I}(h:Aura c a k F)(v:0≤ a): RowCap F k:=by
 obtain ⟨A,C,h,L,g⟩:=h; intro S i; rw [g]; refine le_trans (sum_le_sum (g:=fun j=>saleM a C i j) ?_) (L.rows i); intro j _; rw [Matrix.sum_apply]; refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun T _=> ((h T).pay i j S).trans (le_mul_of_one_le_left ((h T).nonn i j) (rent_one v T)))
lemma RowCap.scale {F:Collected Y I}(h: RowCap F k)(u:ℝ) : RowCap (fun S=>u • F S) (|u| * k):=by intro S i; simp_rw [Matrix.smul_apply,smul_eq_mul,abs_mul, ←mul_sum]; exact mul_le_mul_of_nonneg_left (h S i) (abs_nonneg _)
end Aura
-- crude div/group price. gives uniform analytic without subadditive estimates needed.
lemma chuck (x:ℕ)(p:0<x)(r:ℝ)(v:0≤ r): SumBudget (fun i:ℕ=>r * ((1:ℝ)/2)^(i/x)) (2*x*r):=by
 let f:=fun i:ℕ=> (i/x); apply budget_fiberwise f (fun i=>by positivity) (W:=fun i=>(x*r)*((1:ℝ)/2)^i) ?_ ?_
 · intro k S t; have he:S.card ≤ x:=by apply le_trans (card_le_card_of_injOn (fun i:ℕ=> i%x) (t:=range x) _ _) (card_range x|>.le); exact fun i _=> mem_range.mpr (Nat.mod_lt i p); intro i v j w e; replace hv:= Nat.mod_add_div i x; have hw:=Nat.mod_add_div j x; rw [show i/x = _ from t i v,show i%x=j%x from e] at hv; rw [show k=j/x from (t j w).symm,hw] at hv; exact hv.symm -- tune
   have hv:∑ i∈S,r * ((1:ℝ)/2)^(i/x)= S.card* (r*((1:ℝ)/2)^k):=by rw [← nsmul_eq_mul,←sum_const]; exact sum_congr rfl fun i p=>by rw [show i/x=_ from t i p]; -- tune infer
   rw [hv, mul_assoc]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (by positivity)
 apply budget_loosen (budget_geometric (by positivity : 0≤ (x*r)) (by norm_num : 0 ≤ (1:ℝ)/2) (by norm_num)); exact Eq.le (by ring)
end YM.CF.BPress.Weave
