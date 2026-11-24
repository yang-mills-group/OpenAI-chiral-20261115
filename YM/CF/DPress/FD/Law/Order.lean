import YM.CF.DPress.FD.Law.Fort
/-!
# Finite-dependence bookkeeping including unions of footprints
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Set Lattice MeasureTheory ProbabilityTheory Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {X Y Z I J:Type*}[Fintype I][Fintype J][MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z]
variable {G:I→ I→Prop}{P:Measure X}
abbrev Meeting (G:I→ I→ Prop)(S T:Finset I):Prop:=∀ i∈S,∀ j∈T,G i j
-- use implicit C
abbrev Uses {I Y:Type*}(f:I→Y)(T:Setoid I):Prop:=∀ i j:I,T.r i j→f i=f j
structure OrderF (G:I→ I→Prop)(P: Measure X) where
 see : Finset I→Setoid X
 more : ∀ S T, S⊆ T →∀ i j,(see T).r i j→(see S).r i j
 pair : ∀ S T,Meeting G S T→∀ (F K:Set X),MeasurableSet F→MeasurableSet K→Uses (·∈F) (see S)→ Uses (·∈ K) (see T) → P (F∩ K)= P F * P K
namespace OrderF
abbrev concerns(T:OrderF G P){Y:Type*}(f:X→Y)(V:Finset I):Prop:= Uses f (T.see V)
variable (T:OrderF G P)
lemma know {Y:Type*}{S V:Finset I}{f:X→Y}(u:concerns T f S)(t:S⊆ V):concerns T f V:=fun i j l=> u _ _ (T.more S V t i j l)
lemma neat {A:Type*}{S:Finset I}{f:X→A}(v:concerns T f S)(R:Set A): Uses (·∈ f ⁻¹' R) (T.see S):=fun i j d=> by change (f i∈ R)=(f j∈ R); rw [v i j d]
lemma indep {f:X→Y}{g:X→Z}{S U:Finset I}(p:concerns T f S)(t:concerns T g U)(h: Meeting G S U)(v:Measurable f)(e:Measurable g): IndepFun f g P:=by
 rw [indepFun_iff_measure_inter_preimage_eq_mul]; exact fun A B x y=> T.pair S U h _ _ (v x) (e y) (neat T p _) (neat T t _)
variable [IsProbabilityMeasure P]
lemma fall {S:J→Finset I} {F:J→Set X}(p:∀ i,MeasurableSet (F i))(h:∀ i,concerns T (·∈ F i) (S i))(v:∀ i j:J,i≠j→ Meeting G (S i) (S j)) (D: Finset J) : P (⋂ j∈D,F j)=∏ j∈D,P (F j):=by
 induction D using Finset.induction_on with
 | empty=> simp
 | @insert i D s ih=>
    rw [Finset.prod_insert s,← ih, show (⋂ j∈insert i D,F j)=F i∩ (⋂ j∈D,F j) from ?_]; swap; · ext x; simp
    let U:= D.biUnion S; apply T.pair (S i) U _ _ _ (p i) (MeasurableSet.iInter (fun j=> MeasurableSet.iInter (fun _=> p j))) (h i)
    · intro x y t; refine propext ?_; simp only [mem_iInter]; refine forall_congr' fun j=> forall_congr' fun l=>?_ ; have he:S j⊆ U:=Finset.subset_biUnion_of_mem S l; rw [show (x∈F j)=(y∈F j) from T.know (h j) he x y t]
    intro x p y l; obtain ⟨j,v',q⟩:= Finset.mem_biUnion.mp l; exact v i j (fun g=> s (g.symm ▸ v')) x p y q -- tune goals order
lemma supply (S:J→ Finset I){Y:J→ Type*}[∀ i,MeasurableSpace (Y i)](f:∀ i:J,X→Y i)(p:∀ i,Measurable (f i))(h:∀ i,concerns T (f i) (S i))(v:∀ i j:J,i≠j→ Meeting G (S i) (S j)) : MeasurePreserving (fun x i=> f i x) P (Measure.pi fun i=> P.map (f i)):=by
 have ht:=measurable_pi_lambda _ p; refine ⟨ht,Eq.symm (Measure.pi_eq (fun A B=>?_))⟩; rw [Measure.map_apply ht (MeasurableSet.univ_pi B)]; simp_rw [Measure.map_apply (p _) (B _)]; refine (show (P ((fun x i=> f i x) ⁻¹' _)) = P (⋂ i∈Finset.univ,f i ⁻¹' A i) from congrArg _ (by ext;simp [Set.mem_pi])).trans (fall T (fun i=> p i (B i)) (fun i=>neat T (h i) _) v Finset.univ) -- tune
lemma abide (S:J→ Finset I){Y:J→ Type*}[∀ i,MeasurableSpace (Y i)] {C:∀ i,Measure (Y i)} (f:∀ i:J,X→Y i)(p:∀ i, MeasurePreserving (f i) P (C i))(h:∀ i,concerns T (f i) (S i))(v:∀ i j:J,i≠j→ Meeting G (S i) (S j)) : MeasurePreserving (fun x i=> f i x) P (Measure.pi C):=by have ht:=supply T _ f (fun i=>(p i).measurable) h v; simp only [(p _).map_eq] at ht; exact ht
omit [IsProbabilityMeasure P]
end OrderF
end YM.CF.DPress.FD
