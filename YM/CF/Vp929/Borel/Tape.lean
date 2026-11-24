/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Vp929.Borel.Measure
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Set Function MeasurableSpace MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal NNReal
variable {ι I J X Y A B:Type*}
variable [Fintype I][MeasurableSpace X][MeasurableSpace Y]
lemma loomPair (μ:Measure X) (ν:Measure Y)[SigmaFinite μ][SigmaFinite ν]: MeasurePreserving (fun p:(I→X) × (I→Y)=> fun j=>(p.1 j,p.2 j)) ((Measure.pi fun _:I=>μ).prod (Measure.pi fun _:I=>ν)) (Measure.pi fun _:I=> μ.prod ν):=by
 let f(p:(I→X) × (I→Y))(j):=(p.1 j,p.2 j); have ht:Measurable f:= measurable_pi_lambda _ fun i=> ((measurable_pi_apply _).comp measurable_fst).prodMk ((measurable_pi_apply _).comp measurable_snd)
 refine ⟨ht,(Measure.pi_eq_generateFrom (C:=fun _=> Set.image2 (·×ˢ·) {s:Set X|MeasurableSet s} {t:Set Y|MeasurableSet t}) (fun _=>generateFrom_prod) (fun _=> isPiSystem_prod) (fun _=> μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn) ?_).symm⟩
 intro s h; choose u U v V H using h; have W(i):MeasurableSet (s i):= (H i) ▸ MeasurableSet.prod (U i) (V i)
 rw [Measure.map_apply ht (.univ_pi W), show f ⁻¹' (Set.univ.pi s)=(Set.univ.pi u)×ˢ(Set.univ.pi v) by ext; simp [f,Set.mem_pi,←H,forall_and]]; simp [←H,Finset.prod_mul_distrib]
/-- Slice theorem for any independent family by testing individual vs. finset of others. -/
abbrev spice{Y:ι→Type*} (f:∀ i:ι,X→Y i)(S:Finset ι)(x:X)(i:S):= f i x
lemma separate{Y:ι→Type*}[∀i,MeasurableSpace (Y i)](μ:Measure X)[IsProbabilityMeasure μ] (f:∀ i,X→ Y i) (h:∀ i (S:Finset ι), i∉S→ IndepFun (f i) (spice f S) μ): iIndepFun f μ:=by
 apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr; classical intro S sets H; induction S using Finset.induction_on with
 | empty=> simp
 | @insert i S m ih=>
   have hp:= ih fun i h=> H i (Finset.mem_insert_of_mem h); have u:⋂ i∈ S,f i ⁻¹' sets i= spice f S ⁻¹' (Set.univ.pi (fun i:S=>sets i.val)):=by ext x; simp [Set.mem_pi,spice]
   simp only [Finset.prod_insert m,Finset.set_biInter_insert]; rw [u,(h i S m).measure_inter_preimage_eq_mul _ _ (H i (by simp)) (.univ_pi fun i:S=> H _ (Finset.mem_insert_of_mem i.property)),← u,hp]
variable (μ:Measure X)[IsProbabilityMeasure μ][Nonempty X]
private lemma cutoff (S:Finset I)[MeasurableSpace A](f:(I→X)→A)(hf:Measurable f)(h:∀ x y:I→X, spice (fun i (v:I→X)=>v i) S x=spice (fun i (v:I→X)=>v i) S y→ f x=f y):∃ g:(S→X)→A,Measurable g∧ g ∘ spice (fun i (v:I→X)=>v i) S=f:=by
 classical
 let t(w:S→X)(i):= if p:i∈S then w ⟨i,p⟩ else Classical.arbitrary X; have ht: Measurable t:= measurable_pi_lambda _ fun i=> by unfold t; split; apply measurable_pi_apply; exact measurable_const
 exact ⟨f∘t,hf.comp ht,funext fun i=> h _ i (funext fun j=>by simp only [spice,t,j.property,↓reduceDIte])⟩
theorem independenceTape [MeasurableSpace A][MeasurableSpace B]{T S:Finset I}{f:(I→X)→A}{g:(I→X)→B}(hf:Measurable f)(hg:Measurable g)(pf:∀ x y:I→X,(∀ i∈S,x i=y i)→ f x=f y)(pg:∀ x y:I→X,(∀ i∈T,x i=y i)→g x=g y)(p:Disjoint S T): IndepFun f g (Measure.pi fun _=> μ):=by
 obtain ⟨a,z,H⟩:= cutoff S f hf fun x y v=>pf x y fun i j=>congrFun v ⟨i,j⟩; obtain ⟨b,w,F⟩:= cutoff T g hg fun x y v=>pg x y fun i j=>congrFun v ⟨i,j⟩
 have v:iIndepFun (fun i (x:I→X)=> x i) (Measure.pi fun _=> μ):=iIndepFun_pi (X:=fun (_:I)=>id) (fun i=>measurable_id.aemeasurable); rw [← H,← F]; exact (v.indepFun_finset S T p fun i=>measurable_pi_apply i).comp z w
variable {μ}
end YM.CF.VolumeCape.Borel
