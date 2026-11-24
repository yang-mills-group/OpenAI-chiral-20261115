import YM.CF.Buffered.Bing
import Mathlib.Data.PNat.Basic
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Stack.Kern
open Function Filter Lattice RG MeasureTheory Push.SectorMeasure
open scoped BigOperators ENNReal Topology InnerProductSpace ComplexOrder
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
-- alternating products. shift parities so n exponents recover both orientations.
def chainAux (b : ℕ) (F : Kern μ) : Kern μ := match b with
 | 0 => F
 | k+1=> F*chainAux k (star F)
def chain (F : Kern μ) (k:ℕ) := chainAux (k-1) F
theorem chain_succ (F : Kern μ) {k:ℕ} (h:0<k) : chain F (k+1)=F*chain (star F) k := by
 rcases k with _|k; · omega
 rfl
lemma chain_one (F : Kern μ): chain F 1=F := rfl
lemma chain_tail (F : Kern μ) {k:ℕ} (h:0<k) : chain F (k+1) = chain F k * if k%2=0 then F else star F := by
 induction k, h using Nat.le_induction generalizing F with
 | base=> rw [chain_succ _ (by decide), chain_one, chain_one, if_neg (by decide)]
 | succ n h ih=>
    calc
     _ = F*(chain (star F) n * if n%2=0 then star F else star (star F)) := by rw [chain_succ _ (Nat.succ_pos n), ih (star F)]
     _ = _ := by rw [chain_succ _ h, ←mul_assoc]; congr 1; split_ifs <;> first| rfl| omega| simp only [star_star]
-- trace-convolution joins of same parity lengths
lemma chain_star (F : Kern μ) {a : ℕ} (u:0<a): star (chain F a) = if a %2=0 then chain F a else chain (star F) a := by
 induction a, u using Nat.le_induction generalizing F with
 | base=> rw [chain_one,if_neg (by decide), chain_one]
 | succ a u ih =>
    calc
     _ = (if a%2=0 then chain (star F) a else chain F a)*star F := by rw [chain_succ _ u,star_mul,ih (star F),star_star]
     _ = _ := by split_ifs with k p p <;> first| omega | simp [chain_tail _ u, k]

lemma chain_plus (F : Kern μ) {m n : ℕ} (h : 0 < m) (p : 0 < n) : chain F (m+n)= chain F m * chain (if m%2=0 then F else star F) n := by
 induction m,h using Nat.le_induction generalizing F with
 | base=> rw [add_comm 1,chain_succ _ p,chain_one,if_neg (by decide)]
 | succ m h ih=> rw [show m+1+n=m+n+1 from by omega,chain_succ _ (by omega),ih (star F),chain_succ _ h, ←mul_assoc]; congr 1; split_ifs <;> first| omega| rfl| simp only [star_star] -- simplify new right

lemma chain_join (F:Kern μ) {m n:ℕ}(h:0 < m)(p:0 < n)(v:m%2=n%2) : chain F m * star (chain F n) = chain F (m+n):= by
 rw [chain_plus _ h p,chain_star _ p,v]; split_ifs <;> rfl

def power (F : Kern μ) (n:ℕ) := count (chain F n)
lemma power_τ (F:Kern μ){n:ℕ}(hn:0 < n):τ (chain F (n*2)) = (power F n:ℂ):=by rw [mul_two,←chain_join F hn hn rfl]; exact τ_count _
lemma power_nonneg (F:Kern μ) (n:ℕ): 0 ≤ power F n := count_nonneg _
lemma power_norm (F:Kern μ) {n:ℕ} (hn:0 < n) : ‖τ (chain F (n*2))‖=power F n := by rw [power_τ _ hn,Complex.norm_real,Real.norm_of_nonneg]; exact power_nonneg ..
@[simp] lemma power_star (F:Kern μ) {n:ℕ} (hn:0 < n) : power (star F) n = power F n := by
 apply Complex.ofReal_injective; rw [←power_τ (star F) hn,←power_τ F hn]; generalize hv:n*2=x; obtain _|x:=x; · omega
 rw [chain_succ (star F) (by omega:x>0),star_star,τ_cycle, chain_tail F (by omega), if_neg (by omega)]
lemma power_submul (F:Kern μ){m n:ℕ}(u:0 < m)(v:0 < n): power F (m+n) ≤ power F m* power F n := by
 unfold power; rw [chain_plus _ u v]; refine (count_mul ..).trans_eq ?_; split_ifs; rfl; rw [show (chain (star F) n).count=(chain F n).count from power_star F v]
lemma power_monotone (F:Kern μ){n k:ℕ}(u:0 < n)(v:0<k): power F (k*n) ≤ power F n ^ k := by
 induction k,v using Nat.le_induction with
 | base=> simp
 | succ k v ih=> rw [Nat.add_mul,Nat.one_mul,pow_succ]; exact (power_submul _ (by positivity) u).trans (mul_le_mul_of_nonneg_right ih (power_nonneg ..))
lemma power_between (F:Kern μ){m n:ℕ}(u:0 < m)(v:0 < n) (a:ℕ) (p : n + m = a*2): power F a ^ 2 ≤ power F n * power F m := by
 rw [←power_norm _ (by omega:a>0),←p,←chain_join F v u (by omega)]
 exact (τ_schwarz ..).trans_eq (mul_comm ..)
private lemma seqs {f : ℕ→ℝ} (h : ∀ i, 0 ≤ f i) (t : ∀ i, f (i+1)^2 ≤ f i*f (i+2)) (i : ℕ) : f 1^(i+1) ≤ f 0^i*f (i+1):=by
 by_cases e:0<f 1; swap; · rw [show f 1=0 from le_antisymm (le_of_not_gt e) (h 1), zero_pow (Nat.succ_ne_zero i)]; exact mul_nonneg (pow_nonneg (h _) _) (h _)
 have hp(i:ℕ): 0<f (i+1):=by
    induction i with | zero=> exact e | succ i ih=> by_contra! w; have hv:= t i; rw [le_antisymm w (h _),mul_zero] at hv; nlinarith
 have hr(k:ℕ): f 1*f k ≤ f 0*f (k+1):=by
    induction k with
    | zero=> rw [mul_comm]
    | succ k ih=>
      apply le_of_mul_le_mul_right _ (hp k); rw [mul_assoc, ←sq, mul_assoc (f 0)]; apply (mul_le_mul_of_nonneg_left (t k) e.le).trans; rw [←mul_assoc]; grw [ih] -- sign need
      all_goals first| exact h _|exact le_of_eq (by ring)
 induction i with
 | zero=> simp
 | succ i ih=>
    rw [pow_succ (f 1), pow_succ (f 0)]
    calc
      _ ≤ f 0^i * f (i+1)* f 1:=mul_le_mul_of_nonneg_right ih e.le
      _ ≤ _ := by simp_rw [mul_assoc]; nth_rw 1 [mul_comm (f (i+1))]; exact mul_le_mul_of_nonneg_left (hr (i+1)) (pow_nonneg (h _) _)

lemma convex_comparison (F:Kern μ){a:ℕ}(v:0 < a) (k:ℕ) : power F (3*a) ^ (k+1) ≤ power F a ^ k * power F ((3+2*k)*a) := by
 let f(i:ℕ):= F.power ((2*i+1)*a)
 have hp : ∀ i, f (i+1)^2 ≤ f i*f (i+2):=fun i=> power_between F (by positivity) (by positivity) _ (by ring)
 have ht := seqs (f:=f) (fun _=>power_nonneg ..) hp k; dsimp [f] at ht; simpa only [mul_one, mul_zero, zero_add,one_mul,show ∀ k:ℕ,2*(k+1)+1=3+2*k from fun k=>by omega] using ht
end YM.CF.Buffered.Stack.Kern
#print axioms YM.CF.Buffered.Stack.Kern.convex_comparison
