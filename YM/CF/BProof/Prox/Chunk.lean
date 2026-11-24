import YM.CF.BProof.Prox.Serial

/-! Infinite power transfer lemma under geometric cost on fixed chunks. Doesn't change
any actual matrix; retain both row/column estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Prox.Show
open Function Filter Matrix Finset MeasureTheory RG Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix
variable {A X E I : Type*}[Fintype A][Fintype I][MeasurableSpace X]
variable {B:Base A}{F:B.Index I}{O:Atmos A X}{t C p q:ℝ} {n:ℕ}

def cushion (C:ℝ)(n i:ℕ):= C*((1/2:ℝ)^(i/n))
lemma cushion_pays (h:0<n)(p:0≤C): SumBudget (cushion C n) ((n:ℝ)*C*2):=by
 have H(t:ℕ)(s:Finset ℕ)(g:∀ i∈s,i/n=t) : s.card ≤ n := by
    let f(i:ℕ):= i % n
    apply le_trans (Finset.card_le_card_of_injOn (t:= Finset.range n) f (fun i hi=>Finset.mem_range.mpr (Nat.mod_lt i h)) ?_) (by rw [Finset.card_range])
    intro x hx y hy e; have he:x/n=y/n:=(g x hx).trans (g y hy).symm; simpa only [Nat.div_add_mod] using (show n*(x/n)+x%n=n*(y/n)+y%n from by rw [he]; rw [show x%n=y%n from e]) -- tune
 let z:= (n:ℝ)*C; rw [show (n:ℝ)*C*2=z*(1-(1/2:ℝ))⁻¹ by dsimp [z]; norm_num]; apply budget_fiberwise (fun i:ℕ=>i/n) (fun i=>by unfold cushion; positivity) _ (budget_geometric (by unfold z; positivity : 0≤z) (by norm_num) (by norm_num))
 intro t s g; calc
   _ ≤ ∑ _∈s,(C*(1/2:ℝ)^t) := sum_le_sum (fun i hi=>by rw [cushion,g i hi])
   _ ≤ _ := by unfold z; rw [sum_const,nsmul_eq_mul,mul_assoc]; gcongr ?_*_ ; exact_mod_cast H t s g

variable [DecidableEq I][NormedRing E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable {X':Pup X I E}
theorem chunk (p:0<n)(v:0≤t)(k:0≤C)(h: Show O F F (X'^n) t (1/2))(r:∀ i<n,Show O F F (X'^i) t C) (i:ℕ) : Show O F F (X'^i) t (cushion C n i) := by
 have H(d j:ℕ)(w:j<n) : Show O F F (X'^(d*n+j)) t (C*(1/2)^d) := by
    induction d with | zero=> simp only [zero_mul,zero_add,pow_zero,mul_one]; exact r j w| succ d ih=>
      rw [Nat.succ_mul,Nat.add_right_comm,pow_add,pow_succ, ← mul_assoc]; exact ih.multiply h (by positivity) (by norm_num) v
 have hh:=H (i/n) (i%n) (Nat.mod_lt _ p); rwa [Nat.mul_comm (i/n),Nat.div_add_mod] at hh

end YM.CF.BProof.Prox.Show
