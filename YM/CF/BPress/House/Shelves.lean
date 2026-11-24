import YM.CF.BPress.Law
import YM.CF.BPress.Port.Nook
/-! ways to shuffle to block variables. PM.Count not multiplied by Jacobian. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.House
open RG Wilson Push.SectorMeasure Env MeasureTheory LocalH Lattice Finset Function
open scoped Classical Topology BigOperators
variable {I J F G : Type}[MeasurableSpace F][MeasurableSpace G][Fintype I][Fintype J]
lemma reP {K:Type}[Fintype K](p:Measure F)[IsProbabilityMeasure p](e:K≃ I×J) : MeasurePreserving (fun (f : I→ J→F) (j:K)=> f (e j).1 (e j).2 ) (Law.chain (Law.chain p J) I) (Law.chain p K):= (Law.reindex p e.symm).comp (Port.currMP I J p) -- tune Universe
lemma guest (p:Measure F)[IsProbabilityMeasure p](d:J→I): MeasurePreserving (fun (f:I→J→F) j=>f (d j) j) (Law.chain (Law.chain p J) I) (Law.chain p J):= (Law.keys p (J:=J) (fun i=> (d i,i)) (fun x y g=> Prod.mk.inj g|>.2)).comp (Port.currMP I J p)
abbrev count (X:Type*) [MeasurableSpace X]: Measure X:=Measure.count
lemma counting [Countable F][Countable G][MeasurableSingletonClass F][MeasurableSingletonClass G](g:F≃ G) : MeasurePreserving g (count F) (count G):= by
 refine ⟨measurable_of_countable _, Measure.ext_of_singleton (fun i=>?_)⟩; rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),show ⇑g ⁻¹' {i}={g.symm i} from ?_]; simp [count]; ext x; simp [Equiv.apply_eq_iff_eq_symm_apply] -- tune
lemma count_prod [Countable F][MeasurableSingletonClass F] [Countable G][MeasurableSingletonClass G] : count (F× G)=(count F).prod (count G):= by apply Measure.ext_of_singleton; rintro ⟨x,y⟩; rw [Measure.count_singleton,← Set.singleton_prod_singleton, Measure.prod_prod]; simp [count]
lemma count_pi [MeasurableSingletonClass F][Countable F]:count (I→F)=Law.chain (count F) I:=by apply Measure.ext_of_singleton; intro i; simp [Law.chain,Measure.pi_singleton,count]
abbrev ψprod (I F G:Type)[MeasurableSpace F][MeasurableSpace G] := MeasurableEquiv.arrowProdEquivProdArrow F G I
theorem splitP (I:Type)[Fintype I](p:Measure F)[SigmaFinite p](q:Measure G)[SigmaFinite q]: MeasurePreserving (ψprod I F G) (Law.chain (p.prod q) I) ((Law.chain p I).prod (Law.chain q I)):= measurePreserving_arrowProdEquivProdArrow ..
end YM.CF.BPress.House
