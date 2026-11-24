import YM.CF.BPress.Law
/-! Finite-volume payment combinators for measurability/integrals. uniform estimates elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Filter MeasureTheory RG Wilson Push.SectorMeasure Env
open scoped Topology ENNReal BigOperators Classical
namespace Law
variable {X Z : Type*} [MeasurableSpace X]
lemma fixedP [MeasurableSpace Z] [Norm Z] (c:Z) : Envelope fun _:X=> c:= ⟨measurable_const,‖c‖,fun _=>le_rfl⟩
lemma powerP {𝕜 : Type*} [MeasurableSpace 𝕜][NormedRing 𝕜][MeasurableSpace Z][NormedAddCommGroup Z][Module 𝕜 Z][IsBoundedSMul 𝕜 Z][MeasurableSMul₂ 𝕜 Z]{f : X → 𝕜}{g : X → Z}(p:Envelope f)(q:Envelope g) : Envelope (fun x=> f x • g x) := by
 obtain ⟨C,b⟩:= p.cost; obtain ⟨D,d⟩:= q.cost; exact ⟨p.meas.smul q.meas,C*D, fun x=> (norm_smul_le ..).trans (mul_le_mul (b _) (d _) (norm_nonneg _) ((norm_nonneg _).trans (b x)))⟩
lemma prodP [NormedRing Z][MeasurableSpace Z][MeasurableMul₂ Z]{f g : X→Z}(p: Envelope f)(q:Envelope g): Envelope (fun x=>f x*g x):=by
 obtain ⟨C,b⟩:= p.cost; obtain ⟨D,d⟩:= q.cost; exact ⟨p.meas.mul q.meas,C*D, fun x=> (norm_mul_le ..).trans (mul_le_mul (b _) (d _) (norm_nonneg _) ((norm_nonneg _).trans (b x)))⟩
lemma switchP [Norm Z][MeasurableSpace Z]{f g:X→Z}{P:X→Prop}[DecidablePred P] (b:MeasurableSet {x|P x})(h:Envelope f)(l:Envelope g): Envelope fun x=> if P x then f x else g x:=by
 obtain ⟨C,c⟩:=h.cost; obtain ⟨D,d⟩:=l.cost; refine ⟨Measurable.ite b h.meas l.meas,max C D,fun x=>?_⟩; split; exact (c _).trans (le_max_left ..); exact (d _).trans (le_max_right ..)
lemma addC [MeasurableSpace Z] [NormedAddCommGroup Z][MeasurableAdd₂ Z]{f g : X→Z}(p:Envelope f)(t:Envelope g) : Envelope fun x=> f x+g x:=by
 obtain ⟨C,b⟩:=p.cost; obtain ⟨D,d⟩:=t.cost; exact ⟨p.meas.add t.meas,C+D,fun x=>(norm_add_le ..).trans (add_le_add (b _) (d _))⟩
lemma listP {I:Type*}[MeasurableSpace Z][NormedRing Z][MeasurableMul₂ Z] {f : I→X→Z}(s:List I)(p : ∀ i,Envelope (f i)) : Envelope fun x=> (s.map fun a=>f a x).prod:=by induction s with|nil=>exact fixedP 1| cons i s ih=>exact prodP (p i) ih
lemma partialP {I:Type*} [MeasurableSpace Z][NormedAddCommGroup Z][BorelSpace Z][SecondCountableTopology Z][Fintype I] (A:X→Finset I)(p:∀ i, MeasurableSet {x| i∈ A x}) (f : I → X→ Z)(h:∀ i, Envelope (f i)): Envelope fun x=>∑ i∈ A x,f i x:=by
 rw [show (fun x=> _)= (fun x=> ∑ i,if i∈A x then f i x else 0) from funext fun x=> Eq.symm (by rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter])]; exact Env.total _ fun i=>switchP (p i) (h i) (fixedP (0:Z))
lemma marginalP {Y:Type*} [MeasurableSpace Z][NormedAddCommGroup Z][NormedSpace ℝ Z][BorelSpace Z][SecondCountableTopology Z][MeasurableSpace Y]{f : X× Y→ Z}(p:Envelope f) (μ:Measure Y)[IsProbabilityMeasure μ]: Envelope fun x=>∫ y,f (x,y)∂μ:= Env.marginal (g:=fun x=> f x.swap) (Env.along p measurable_swap) μ
end Law
end YM.CF.BPress
