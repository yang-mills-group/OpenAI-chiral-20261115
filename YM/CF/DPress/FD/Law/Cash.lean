import YM.CF.DPress.FD.Cycle.Park
/-!
# Finite laws (after sampling) at one period

Use finite samples for the cycle colorings and throughout the jitter/symmetrization step.
Allow complicated local observations. Record dependence by a spatial equivalence per site;
then rectangles use those restrictions only.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Filter Finset
open scoped Topology BigOperators ENNReal NNReal Classical
variable {I J K:Type*}[Fintype I][Fintype J][Fintype K]
structure Cash (I:Type*)[Fintype I] where
 μ:I→ℝ
 nn(i): 0≤μ i
 price: ∑ i, μ i =1
namespace Cash
variable (c:Cash I)
abbrev turn (P:I→Prop):ℝ:= ∑ i:I with P i, c.μ i
lemma size (P:I→Prop):0≤turn c P:=sum_nonneg (fun i _=> c.nn i)
lemma mint : turn c (fun _=>True)=1:=by unfold turn; simp [c.price]
lemma tape {P Q:I→Prop}(t:∀ i,P i↔ Q i):turn c P=turn c Q:=by congr; exact funext (fun i=>propext (t i))
lemma vivid :∃ i,0<c.μ i:=by by_contra! h; have he: ∑ i,c.μ i=0:= sum_eq_zero fun i _=> le_antisymm (h i) (c.nn i); rw [c.price] at he; exact one_ne_zero he
lemma nilP(P:I→Prop)(h:∀ i,¬ P i):turn c P=0:=sum_eq_zero fun i u=>False.elim (h i (mem_filter.mp u).2)
include c in
lemma ok :Nonempty I:= let ⟨i,_⟩:= vivid c; ⟨i⟩
-- independence via simultaneous payments for every possible projection. Orientation fine equivalence not necessarily the discrete letter.T.T.
abbrev Holds {U:Type*}(f:I→U)(R:Setoid I) := ∀ i j,R.r i j→f i=f j
abbrev Pair (R S:Setoid I):Prop:= ∀ x y:I, turn c (fun z=>R.r z x ∧ S.r z y)=turn c (fun z=> R.r z x)*turn c (fun z=> S.r z y)
def ruleFx {I:Type*}{Y:Type*}(f:I→Y):Setoid I where
 r x y:= f x=f y
 iseqv:= ⟨fun _=>rfl,Eq.symm,Eq.trans⟩
abbrev Keep(I:Type*):Setoid I:= ⟨fun _ _=>True,⟨fun _=>trivial,fun _=>trivial,fun _ _=>trivial⟩⟩
lemma swiv(R:Setoid I) : Pair c R (Keep _):=fun x y=>by rw [tape c (P:=fun z=>R.r z x∧(Keep I).r z y) (Q:=fun z=> R.r z x) (fun i=> ⟨And.left,fun p=>⟨p,trivial⟩⟩), show turn c (fun z=> (Keep I).r z y)=1 from mint c,mul_one]
lemma Pair.sym {R S:Setoid I}(p:Pair c R S):Pair c S R:=fun x y=> by rw [tape c (Q:=fun z=> R.r z y ∧ S.r z x) (fun z=> and_comm), p, mul_comm]
-- extension to all holds via quotient. also to restricted readings.B.
private theorem partition {R:Setoid I}(P:I→Prop): turn c P=∑ x: Quotient R,turn c (fun i=> Quotient.mk R i=x ∧ P i):=by
 unfold turn; simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i _; simp [ite_and]
private lemma unit_r {R S:Setoid I}(p:Pair c R S)(x:Quotient R)(y:Quotient S) : turn c (fun i=> Quotient.mk R i=x∧ Quotient.mk S i=y)= turn c (fun i=>Quotient.mk R i=x)*turn c (fun i=>Quotient.mk S i=y):=by
 induction x using Quotient.inductionOn; rename_i x; induction y using Quotient.inductionOn; rename_i y; simp only [Quotient.eq]; exact p x y
lemma region {R S:Setoid I}(p:Pair c R S) (P Q:I→Prop)(u:Holds P R)(v:Holds Q S): turn c (fun i=> P i∧ Q i)=turn c P*turn c Q:=by
 have ht(R:Setoid I)(P Q:I→Prop)(u:Holds P R)(x:Quotient R): turn c (fun i=> Quotient.mk R i=x∧(P i∧Q i))=(if P x.out then turn c (fun i=>Quotient.mk R i=x∧ Q i) else 0):=by
    have he(i:I)(h:Quotient.mk R i=x):P i=P (Quotient.out x):=u i x.out (Quotient.eq.mp (h.trans (Quotient.out_eq x).symm))
    split; next p=> apply tape; intro i; exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,he i h.1 ▸ p,h.2⟩⟩
    next p=> exact nilP c _ fun i h=>p (he i h.1 ▸ h.2.1)
 have hg(x:Quotient R):turn c (fun i=> Quotient.mk R i=x ∧ Q i)= turn c (fun i=>Quotient.mk R i=x)*turn c Q :=by
    rw [partition c (R:=S),partition c (R:=S) Q,mul_sum]; apply sum_congr rfl; intro y _; rw [tape c (Q:=fun i=> Quotient.mk S i=y∧ (Q i∧Quotient.mk R i=x)) (fun i=>by grind), ht S Q _ v y]; have he:=ht S Q (fun _=>True) v y; simp only [and_true] at he; rw [he]; split_ifs with h; exact (unit_r c (Pair.sym c p) y x).trans (mul_comm ..); rw [mul_zero]
 rw [partition c (R:=R),partition c (R:=R) P,sum_mul]; apply sum_congr rfl; intro i _; rw [ht R P Q u i]; have he:= ht R P (fun _=>True) u i; -- simp 
 simp only [and_true] at he; rw [he]; split_ifs with h; exact hg i; rw [zero_mul]

end Cash
end YM.CF.DPress.FD
