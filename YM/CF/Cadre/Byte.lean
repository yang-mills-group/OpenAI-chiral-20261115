import YM.CF.Cadre.Clear
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
abbrev plough(A:Type*)[Fintype A]:=leaf A→ℝ
abbrev veil(K T U: plough A)(o:A):= ∑ X∈spark o,K X*T X* U X
variable (s: Palot.leaf A→ℝ)(V K:Palot.leaf A→ℝ)(hs:0≤s)(h:0≤V)(q:0≤K)(a b:ℝ)(c d:ℝ)
abbrev fog (Y:leaf A):=K Y*s Y* waveL a Y
local notation "Ω"=> (fog s K a)
local notation "w7"=> farW A
abbrev vaultℜ (P Q K':ΣA→ℝ)(o:A):=∑ X∈ spark o, (∑ Y:ΣA, ode0 Q P X Y)* K' X
abbrev nook (V:ΣA→ℝ)(o:A):=∑ i∈spark o,V i
abbrev shelfR (V:ΣA→ℝ)(o:A):=∑ i∈spark o,V i*i.val.card
lemma canal(K V:ΣA→ℝ)(o:A):
 (∑ Y:ΣA, K Y*∑ X∈spark o∩ blaze Y,V X)=∑ X∈spark o,V X* ∑ Y∈blaze X,K Y:=by
 simp_rw [mul_sum]; have he (X Y:ΣA):Y∈blaze X↔X∈blaze Y:=by unfold blaze; simp [disjoint_comm]
 have hp(Y:ΣA): (∑ X∈spark o∩blaze Y,K Y*V X)=∑ X∈spark o,if Y∈blaze X then K Y*V X else 0:=by
    rw [←sum_filter]; congr 1; ext j; simp [spark,blaze,disjoint_comm]
 simp_rw [hp]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [←sum_filter]; refine sum_congr ?_ ?_; ext j; rw [mem_filter,and_iff_right (mem_univ _)]; intro j _; rw [mul_comm]
variable (sx:∀ (G H:Palot.leaf A)(i: Palot.hook A),i∈drum G H ∅→s G ≤ s H*tilt s i)(hv:∀ i:A,nook (V*s) i ≤ a)(hQ:∀ i:A,nook (fog s K a) i ≤ b)(hT:∀ i:A,shelfR (fog s K a) i ≤ c)
include h q hs sx hv hQ hT
lemma vale (o:A)(ha:0 ≤ a) : vaultℜ V K s o ≤ c*a+ shelfR (V*s) o*b:=by
 unfold vaultℜ; simp_rw [sum_mul]; rw [sum_comm]; refine (sum_le_sum fun i _=> aura i o K V s q h hs sx hv).trans ?_
 have ht:0≤ Ω:=fun i=> mul_nonneg (mul_nonneg (q i) (hs i)) (Real.exp_pos ..|>.le); rw [sum_add_distrib,←sum_filter]
 apply add_le_add; · refine le_trans ?_ (mul_le_mul_of_nonneg_right (hT o) ha); unfold shelfR spark; rw [sum_mul]; exact Finset.sum_le_sum fun i v=> le_of_eq (by unfold fog; simp only [Pi.mul_apply]; ring)
 rw [canal]; -- check shelf unfolded by simp_rw sum_mul earlier
 refine sum_le_sum fun i _=>?_ ; change (V i*s i)* _ ≤ V i*s i*i.val.card * b; rw [mul_assoc (V i*s i) (i.val.card:ℝ)]; apply mul_le_mul_of_nonneg_left; exact beam i Ω ht b fun i _=>hQ i; exact mul_nonneg (h i) (hs i)
-- full plus exactly one birth. masks combin
end YM.CF.Cadre
