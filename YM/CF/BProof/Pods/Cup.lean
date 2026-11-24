/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.BProof.Contour.Margin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Count

/- independent block coordinates transport. `portion` and projection eqs; measure real changes. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Pods
open Function Filter MeasureTheory Relation Finset RG
open Set Measure
open scoped Topology BigOperators Classical ENNReal
variable {B I J:Type}[Fintype B][DecidableEq B][Fintype I][DecidableEq I][Fintype J][DecidableEq J] (X Y:B→Type) (A:I→Type)
variable [∀ i,MeasurableSpace (X i)][∀ i,MeasurableSpace (Y i)][∀ i,MeasurableSpace (A i)]

section Enumerate
lemma count_pi [∀ i,Fintype (X i)][∀ i,MeasurableSingletonClass (X i)]: Measure.pi (fun i=> (Measure.count: Measure (X i)))=(Measure.count: Measure ((i:B)→ X i)):=by
 have h(A: (i:B)→ X i) : (Measure.pi (fun i=> (Measure.count:Measure (X i)))) ({A}: Set ((i:B)→X i))=1:=by rw [Measure.pi_singleton]; simp
 exact Measure.ext_of_singleton (fun i=> by rw [h]; simp) -- tune ext
lemma cost_measure (T:Type)[Fintype T][MeasurableSpace T][MeasurableSingletonClass T] : Measure.count.real (Set.univ:Set T)=Fintype.card T:=by simp [measureReal_def,count_apply MeasurableSet.univ]
lemma count_all_finite (T:Type)[Fintype T][MeasurableSpace T] : IsFiniteMeasure (Measure.count:Measure T):= inferInstance
lemma count_asks [MeasurableSpace I][MeasurableSingletonClass I] {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](f:I→V): (∫ i,f i ∂Measure.count)=∑ i,f i:=by rw [integral_count]; -- tune
end Enumerate
-- block fibers
section Pad
variable (f:I→B)
abbrev Fiber(b:B):= {i // f i=b}
abbrev Pad (b:B): Type:= (i:Fiber f b)→ A i
def levy (x:(i:I)→ A i) : (b:B)→ Pad A f b := fun _ i=> x i
abbrev dress(x:(b:B)→Pad A f b)(i:I):A i:= x (f i) ⟨i,rfl⟩
lemma straight(x:(b:B)→ Pad A f b): levy A f (dress A f x)=x:=by funext i j; obtain ⟨j,h⟩:=j; subst i; rfl
def tape : ((b:B)→Pad A f b) ≃ᵐ ((i:I)→ A i):= ⟨⟨dress A f, levy A f,straight A f,fun _=>rfl⟩,by simp only [Equiv.coe_fn_mk]; fun_prop,by simp only [Equiv.coe_fn_symm_mk]; unfold levy; fun_prop⟩
abbrev pool(μ:∀ i,Measure (A i))(b:B): Measure (Pad A f b):= Measure.pi fun i=> μ i
lemma wet(μ:∀ i, Measure (A i))[∀ i, SigmaFinite (μ i)] : MeasurePreserving (tape A f) (Measure.pi (pool A f μ)) (Measure.pi μ):=by
 let e:=tape A f; refine ⟨e.measurable,Eq.symm (Measure.pi_eq ?_)⟩; intro T h; let V(b:B):=Set.univ.pi fun i:Fiber f b=> T i
 have hp:e ⁻¹' Set.univ.pi T=Set.univ.pi V:=by ext x; refine ⟨fun p i _ j a=>?_,fun p i _=>p (f i) (Set.mem_univ _) (⟨i,rfl⟩:Fiber f (f i)) (Set.mem_univ _)⟩; obtain ⟨j,t⟩:=j; subst i; exact p j (Set.mem_univ _)
 rw [Measure.map_apply e.measurable (MeasurableSet.univ_pi h),hp,Measure.pi_pi]; unfold pool V; simp_rw [pi_pi]; exact Fintype.prod_fiberwise f (fun i=>μ i (T i)) -- tune tape e
end Pad
section Merge
variable (μ:∀ i, Measure (X i)) (ν:∀ i,Measure (Y i))[∀ i, SigmaFinite (μ i)][∀ i, SigmaFinite (ν i)]
abbrev meet (i:B):= X i× Y i
abbrev ux (x:(i:B)→meet X Y i)(i:B):= (x i).1
abbrev uy (x:(i:B)→meet X Y i)(i:B):= (x i).2
def divide : ((i:B)→ meet X Y i) ≃ᵐ ((i:B)→X i)×((i:B)→Y i):= ⟨⟨fun i=>(ux X Y i,uy X Y i),fun x i=>(x.1 i,x.2 i),fun i=>rfl,fun i=>rfl⟩,by simp only [Equiv.coe_fn_mk]; unfold ux uy; fun_prop,by simp only [Equiv.coe_fn_symm_mk]; fun_prop⟩
abbrev milk (i:B):= (μ i).prod (ν i)
-- adaptation of measurePreserving_arrowProdEquivProdArrow to dependent coords
lemma mp_div : MeasurePreserving (divide X Y) (.pi (milk X Y μ ν)) ((Measure.pi μ).prod (Measure.pi ν)):=by
 let e:= divide X Y; refine ⟨e.measurable,Eq.symm ?_⟩
 refine FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i=> (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i=> (ν i).toFiniteSpanningSetsIn))) ?_
 · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm -- tune orientation
   · exact (FiniteSpanningSetsIn.pi (fun i=> (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
   exact (FiniteSpanningSetsIn.pi (fun i=> (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
 rintro _ ⟨s',⟨s,-,rfl⟩,t',⟨t,-,rfl⟩,rfl⟩
 have ht:e ⁻¹' ((Set.univ.pi s) ×ˢ (Set.univ.pi t))=Set.univ.pi (fun i=>s i ×ˢ t i):=by ext i; simp [e, divide,MeasurableEquiv.coe_mk, Set.mem_pi, forall_and]; -- tune
 rw [MeasurableEquiv.map_apply, ht,prod_prod]; unfold milk; simp_rw [pi_pi, prod_prod, Finset.prod_mul_distrib]
end Merge
end YM.CF.BProof.Pods
