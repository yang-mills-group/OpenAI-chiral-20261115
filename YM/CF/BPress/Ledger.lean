import YM.CF.Support.Grove
import YM.Push.ABSOLUTE_SUMS.Basic
/-! Generic function-array cost in B eq:B-wn etc. grade arith & representation over ONE term per support (accumulate absolutely, keeping connectivity as a given property, total sup on variables admitted); other protocols included by allowing reach smaller, query local equivalence predicates outside the arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Finset Filter Lattice Push.AbsoluteSums RG Branch
open scoped Topology BigOperators Classical
namespace Ledger
variable {X D K I J : Type*} [DecidableEq X][Fintype X]
abbrev RangeT (F : Branch.Field X):= {S: Finset X // Grove F S}
-- use Finset supports over all (allow fees zero, no reliance on DecidablePred Grove later).
variable (r : I→Finset X)(b : I→ℝ)
def score (a:ℝ)(x:X)(i:I):= if x∈r i then Real.exp (a*(r i).card)*b i else 0
/-- Every site hit priced. keep b even on zero-score (empty/disconnected unused handles). -/
structure Cash (a C:ℝ) : Prop where
 pos (i): 0≤b i
 hits (x:X): SumBudget (score r b a x) C

section lemmas
variable {r b} {c : I→ ℝ} {a g C E : ℝ}
lemma Cash.chill (p : Cash r b a C)(v:g ≤ a): Cash r b g C:= by
 refine ⟨p.pos,fun i=>budget_mono (p.hits i) (fun x=>?_) (fun x=>?_ )⟩ <;> unfold score <;> split
 · next h=> have he := p.pos ‹I›; positivity
 · exact le_rfl
 · gcongr; apply p.pos
 · exact le_rfl
lemma Cash.subs (p : Cash r b a C)(h:∀ i,0≤c i)(t:∀ i,c i≤b i): Cash r c a C:= ⟨h,fun i=> budget_mono (p.hits i) (fun x=> by unfold score; split; exact mul_nonneg (Real.exp_pos _).le (h _); rfl) fun x=> by unfold score; split; exact mul_le_mul_of_nonneg_left (t _) (Real.exp_pos _).le; rfl ⟩
lemma Cash.plus (p:Cash r b a C)(h:Cash r c a E): Cash r (fun i=>b i+c i) a (C+E):= by refine ⟨fun i=> add_nonneg (p.pos i) (h.pos i), fun x=>?_⟩; convert budget_plus (p.hits x) (h.hits x) using 1; ext; unfold score; split <;> simp [mul_add]
lemma Cash.scale (k:ℝ)(p:Cash r b a C)(h:0≤k): Cash r (fun i=>k*b i) a (k*C):=by
 refine ⟨fun i=>mul_nonneg h (p.pos i), fun x=>?_⟩; convert budget_scale h (p.hits x) using 1; ext; unfold score; split <;> ring
lemma Cash.weaken (p:Cash r b a C)(h:C≤E):Cash r b a E:=⟨p.pos,fun i=>budget_loosen (p.hits i) h⟩
lemma Cash.zero [Nonempty X](p:Cash r b a C) : 0≤ C:= budget_nonneg (p.hits (Classical.arbitrary X))
lemma exp_one (F:Finset X)(a:ℝ)(p:0≤a): 1≤Real.exp (a*F.card):= Real.one_le_exp (by positivity)
lemma Cash.single (p:Cash r b a C)(u:0≤a)(i:I)(k:(r i).Nonempty): b i≤ C:=by obtain ⟨x,h⟩:=k; exact le_trans (le_mul_of_one_le_left (p.pos _) (exp_one (r i) a u)) (Eq.le (if_pos h|>.symm)|>.trans (budget_single (p.hits x) i))
lemma Cash.total (p:Cash r b a C) (k:0≤a)(v:∀ i,r i=∅→ b i=0): SumBudget b ((Fintype.card X:ℝ)* C):=by
 have he := budget_over univ (fun x=> score r b a x) _ fun x _=> p.hits x; rw [sum_const,nsmul_eq_mul,card_univ] at he; refine budget_mono he p.pos (fun i=>?_ ); rcases (r i).eq_empty_or_nonempty with h|⟨x,h⟩; rw [v i h]; exact he.1 i; exact le_trans (le_mul_of_one_le_left (p.pos _) (exp_one (r i) a k)) ((if_pos h).symm.le.trans (single_le_sum (f:=fun x=>score r b a x i) (fun i' _=>(p.hits i').1 _) (mem_univ x)))
end lemmas
section bundle
variable [NormedAddCommGroup K] [CompleteSpace K]
-- regroup preserving the precise support to use Mark comparisons of values. no Option/PartRn selectors needed.
def lump (r : I → J) [DecidableEq J] (f : I→ K) (t:J) : K:= ∑' i, if t=r i then f i else 0
lemma lump_sum (r:I→J)[DecidableEq J][Fintype J](f : I→K)(p:Summable f): ∑ t,lump r f t=∑' i,f i:=by
 unfold lump; rw [← Summable.tsum_finsetSum _]; apply tsum_congr; intro i; simp;
 intro x _; convert! p.indicator {i:I| x=r i} using 1; funext i; by_cases v: x=r i <;> simp [Set.indicator,v]
lemma lump_bound (r:I→J)[DecidableEq J](b : I→ℝ)(f:I→ K)(v: Summable b)(p:∀ i, ‖f i‖ ≤ b i)(t:J): ‖lump r f t‖ ≤ lump r b t:=by
 let F(i:I):= if t=r i then f i else 0; let g(i:I):= if t=r i then b i else 0; have hx(i):‖F i‖≤ g i:=by unfold F g; split; exact p i; simp
 have hv:Summable g:=by convert! v.indicator {i|t=r i} using 1; funext i; by_cases p:t=r i <;> simp [Set.indicator,g,p]
 have hf := summable_of_sum_le (fun i=> norm_nonneg (F i)) (fun s=> (sum_le_sum (fun i _=> hx i)).trans (hv.sum_le_tsum s fun i _=> (norm_nonneg _).trans (hx i))); -- tune arg order
 exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hx hv)
end bundle
lemma Cash.lump {a C : ℝ}(p: Cash r b a C)(v : Summable b) : Cash id (lump r b) a C:=by
 refine ⟨fun t=> tsum_nonneg fun _=> (ite_nonneg (p.pos _) le_rfl),fun x=>?_⟩ -- tune
 convert (show SumBudget (Ledger.lump r (score r b a x)) C from ⟨fun t=> tsum_nonneg fun _=> ite_nonneg ((p.hits x).1 _) le_rfl,summable_of_finite_support (Set.toFinite _),by rw [tsum_fintype,lump_sum r _ (p.hits x).2.1]; exact (p.hits x).2.2⟩) using 1; ext t; unfold score Ledger.lump id; split; next k=>
    rw [← tsum_mul_left]; apply tsum_congr; intro i; split; next q=> dsimp only; rw [←q,if_pos k]
    simp
 · symm; apply HasSum.tsum_eq; apply hasSum_zero.congr_fun; intro i; by_cases h:t=r i <;> simp_all
end Ledger
end YM.CF.BPress
