import YM.CF.Roots.Watt
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}{u t B:ℕ}{C ε η a d:ℝ}
variable {J X:Type}[Fintype J][LinearOrder J][Fintype X][DecidableEq X]
local notation "ζ"=> Finset J
variable (σ:J→Site n)(c: Site n)
variable (Φ:X→Support n)(U:X→Prop) [DecidablePred U]
abbrev cocoa (Θ:X→Support n)(U:X→Prop)[DecidablePred U](X:X)(a:ℝ)(B:ℕ):ℝ:= if U X then dra_k B a (Θ X) else 0
variable (pS:Apex (cape_B B) B σ)(pH:lamp_B (cape_B B) B t σ)
local notation "Δ"=> (a+1/2)
include pH
variable (V:Finset (Finset J))(f : Finset J→ X→ℝ)(p:∀ i∈V,0 ≤ f i)(uξ:∀ i∈V,∀ x:X, U x→f i x≠0→ c∈ Φ x∧poke_F σ (Φ x) i)(b K:ℝ)(hr:∀ i∈V,∑ x:X,cocoa Φ U x (a+1/2) B*f i x≤ b)(hx:0≤b)(z:Finset J→ℂ)(hz:∀ i∈V,‖z i‖ ≤ C^i.card)(pC:1 ≤ C)(hk:8≤B)(w:Nice_B B t C (1/8))
local notation "Uo"=> fun i:Finset J=> fun x=> if U x then f i x else 0
include p hr uξ hx pC hz w hk
lemma πRoot (vt:(∀ i∈V,i.card=1 ∧ (t*C*b+wish_E B b≤K)))(h:0≤ K) : ∑ x:X,cocoa Φ U x a B*(∑ i∈V,‖z i‖*f i x) ≤ K:=by
 rw [show (fun x:X=>cocoa Φ U x a B*(∑ i∈V,‖z i‖*f i x))=(fun x=>∑ i∈V, ‖z i‖*(dra_k B a (Φ x)*Uo i x)) from ?_,Finset.sum_comm] -- notation parens scope
 swap
 · funext x; unfold cocoa; split
   next v=> rw [Finset.mul_sum]; exact sum_congr rfl (fun i t=>by dsimp only; rw [if_pos v,mul_left_comm])
   next v=> simp only [zero_mul,if_neg v,mul_zero,sum_const_zero]
 let F:= Uo; have pF(i)(e:i∈V):0≤ F i:= fun x=>by unfold F; split; exact p _ e _; exact le_rfl
 have he(i)(v:i∈ V): ∑ x:X,dra_k B (a+1/2) (Φ x)*F i x ≤ b:=by
    refine le_trans (le_of_eq ?_) (hr i v); apply sum_congr rfl; intro j _; unfold F cocoa; split <;> simp [*] -- careful
 have ht:= tiny_Q σ c Φ F V pF (fun i v x p=>by unfold F at p; split at p; exact uξ i v x (by assumption) p; contradiction) pC hk pH w b he hx (fun i e=>(vt i e).1)
 by_cases hg:V.Nonempty
 · obtain ⟨i,v⟩:=hg; simp_rw [← Finset.mul_sum]; refine (sum_le_sum (g:=fun i=>C^i.card*∑ x:X,dra_k B a (Φ x)*F i x) (fun i v=>mul_le_mul_of_nonneg_right (hz i v) (sum_nonneg fun j _=>mul_nonneg (Real.exp_pos _).le (pF i v j)))).trans (ht.trans (vt i v).2)
 rw [Finset.not_nonempty_iff_eq_empty.mp hg,sum_empty]; exact h
include pS
lemma ΦRoot (vt:∀ i∈V, 1 < i.card)(h:∀ i∈V,Set.InjOn σ (i:Set J))(wv:wish_E B b ≤ K): ∑ x:X,cocoa Φ U x a B*(∑ i∈V,‖z i‖* f i x) ≤ K:=by
 let F:=Uo
 rw [show (fun x:X=>cocoa Φ U x a B*(∑ i∈V,‖z i‖*f i x))=(fun x=>∑ i∈V, ‖z i‖*(dra_k B a (Φ x)*F i x)) from ?_,Finset.sum_comm] -- notation parens scope
 swap
 · funext x; unfold cocoa; split
   next v=> rw [Finset.mul_sum]; exact sum_congr rfl (fun i t=>by unfold F; rw [if_pos v,mul_left_comm])
   next v=> simp only [F,zero_mul,if_neg v,mul_zero,sum_const_zero]
 have pF(i)(e:i∈V):0≤ F i:= fun x=>by unfold F; split; exact p _ e _; exact le_rfl
 have he(i)(v:i∈ V): ∑ x:X,dra_k B (a+1/2) (Φ x)*F i x ≤ b:=by
    refine le_trans (le_of_eq ?_) (hr i v); apply sum_congr rfl; intro j _; unfold F cocoa; split <;> simp [*]
 have ht:= many_F σ c Φ F V pF (fun i v x p=>by unfold F at p; split at p; exact uξ i v x (by assumption) p; contradiction) pC hk pS pH w b he hx h vt
 simp_rw [← Finset.mul_sum]; refine (sum_le_sum (g:=fun i=>C^i.card*∑ x:X,dra_k B a (Φ x)*F i x) (fun i v=>mul_le_mul_of_nonneg_right (hz i v) (sum_nonneg fun j _=>mul_nonneg (Real.exp_pos _).le (pF i v j)))).trans (ht.trans wv)
end YM.CF.Roots
