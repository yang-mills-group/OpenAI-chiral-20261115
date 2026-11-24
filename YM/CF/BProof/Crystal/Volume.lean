import YM.CF.BProof.Crystal.Shard
/-! Expansion identity including coefficients. Lifted terms written to use
localized measurements of activities only. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Crystal
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Sprinkle
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I U: Type}[DecidableEq V][Fintype V][Fintype I][LinearOrder I][Fintype U] [DecidableEq U]
def fossil{F:Type*}[DecidableEq F](S:Finset F)(g:F→ℂ)(h:F→Dough I): ∀ x:Unit, FC I:=fun _=> star (∏ i∈S,g i) • (∏ i∈S,h i).val -- tune remove
lemma fossil_eq {F:Type*}[DecidableEq F](S:Finset F)(g:F→ℂ)(h:F→Dough I)(f:F→Dough I)(e:∀ i,(f i).val=star (g i) • (h i).val): (∏ i∈S,f i).val=star (∏ i∈S,g i) • (∏ i∈S,h i).val:=by
 induction S using Finset.induction_on with
 | empty=> simp -- tune
 | insert i S k ih=>
    rw [prod_insert k,prod_insert k,prod_insert k,star_mul]; change ((f i).val *(∏ i∈S,f i).val)=_ • ((h i).val * (∏ i∈S,h i).val); rw [ih,e, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_smul]; rw [smul_comm]
namespace Dew
variable (P:Dew V I){S:Finset V}
lemma flareB (F:I→I→U→ℂ)(i:P.Box U) : (P.flare F i).val=star (P.flareC F i) • (P.flareL i).val:=fossil_eq univ _ _ _ (fun _=> hollow_face ..)
lemma digest_p(F:I→I→U→ℂ)(S: Finset (P.Box U)): (P.digest F S).val= star (P.lc F S) • (P.light S).val:=fossil_eq _ _ _ _ (P.flareB F)
def notch (S:Finset (P.Box U))(T:Finset V):ℂ:= inner ℂ (acts (P.light S).val (vacuum I)) (acts (P.beam T).val (vacuum I))
lemma notch_pay (S:Finset (P.Box U))(T:Finset V) : ‖P.notch S T‖≤ 1:=by
 let p:=vacuum I; apply le_trans (norm_inner_le_norm (𝕜:=ℂ) ..); apply mul_le_one₀ ?_ (norm_nonneg _) ?_
 · apply (actuary ..).trans; rw [show ‖vacuum I‖=1 by simp [vacuum,basisKet],mul_one]; exact P.lightcost S
 apply (actuary ..).trans; rw [show ‖vacuum I‖=1 by simp [vacuum,basisKet],mul_one]; exact P.beamMoney T
lemma gushF(C:Op I)(F:I→I→U→ℂ)(h:∀ i j,i<j→ C i j=∑ k:U,F i j k)(x:Cᵀ= -C)(S:Finset V)(f:P.terse S): P.magic C S=∑ i∈Sprinkle.span (fun i=>P.Lease i U) S,P.lc F i * P.notch i S:=by
 rw [magic,glance _ _ (homeZone (P.beamAt S)),spool _ (P.area S) x,P.electrify C F h S f]; let Y:=P.beam S; change inner ℂ (acts ((Dough I).val _) _) _=_; rw [map_sum,act_sum,sum_inner]; apply sum_congr rfl; intro i hi; rw [show (Dough I).val (P.digest F i)=_ from P.digest_p F i, act_smul, inner_smul_left]; change star (star _) * _=_; rw [star_star]; rfl
-- relate down supports mild etc to lifted
abbrev Honest (S:Finset (P.Box U)):= P.mild (down S) ∧ P.terse (down S)
def silica (A:V→ℂ)(C:Op I)(S:Finset V):ℂ:= if P.mild S then (∏ i∈ S,A i)*P.magic C S else 0
def litmus(A:V→ℂ)(F:I→I→U→ℂ)(i:P.Box U):ℂ:= A i.1* P.flareC F i
def quint(A:V→ℂ)(F:I→I→U→ℂ)(S:Finset (P.Box U)):ℂ:= (∏ i∈ S,P.litmus A F i)*P.notch S (down S)
def quartet(A:V→ℂ)(F:I→I→U→ℂ)(S:Finset (P.Box U)):ℂ:= if Smooth S∧P.Honest S then P.quint A F S else 0
lemma gush(C:Op I)(A:V→ℂ)(F:I→I→U→ℂ)(h:∀ i j,i<j→ C i j=∑ k:U,F i j k)(x:Cᵀ= -C)(S:Finset V): P.silica A C S=∑ i∈ Sprinkle.span (fun i=>P.Lease i U) S,P.quartet A F i:=by
 by_cases t:P.mild S ∧ P.terse S; · rw [silica,if_pos t.1,P.gushF C F h x S t.2,mul_sum]; apply sum_congr rfl; intro i hi; obtain ⟨a,b⟩:= (mem_span ..).mp hi; unfold quartet quint litmus; rw [if_pos ⟨a, (by unfold Honest; rwa [b])⟩, prod_mul_distrib,b,←show ∏ j∈down i,A j = ∏ j∈S,A j from (by rw [b]), prod_image a, mul_assoc]; rfl
 rw [sum_eq_zero]; · unfold silica; split; rw [magic,P.beamZero (fun h=> t ⟨‹_›,h⟩), show (0:Dough I).val=(0:FC I) from rfl, act_zero, inner_zero_right, mul_zero]; rfl
 intro i hi; rw [quartet,if_neg]; intro v; obtain ⟨a,b⟩:=v; unfold Honest at b; rw [(mem_span ..|>.mp hi).2] at b; exact t b
lemma sip (C:Op I)(A:V→ℂ)(F:I→I→U→ℂ)(h:∀ i j,i<j→ C i j=∑ k:U,F i j k)(x:Cᵀ= -C) : (∑ i:Finset V,P.silica A C i)=∑ j:Finset (P.Box U),P.quartet A F j:=by
 simp_rw [P.gush C A F h x]; rw [←sumDown]; apply sum_congr rfl; intro i _; by_cases g:Smooth i; rw [if_pos g]; simp only [quartet,g,false_and,ite_false]
end Dew
end YM.CF.BProof.Crystal
