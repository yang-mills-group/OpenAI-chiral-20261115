import YM.CF.BProof.Floral.Cord
import Mathlib.Analysis.SpecialFunctions.Exponential
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal Classical
namespace YM.CF.Floral
variable {X E G:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup G][NormedSpace ℂ G]{D:Set ℂ}{C:ℝ}
def SubHol(D:Set ℂ)(f:D→ E):Prop:=∃ F:ℂ→ E,Hol D F∧∀ z:D,F z=f z
def Maker (f:D→ E)(x:ℂ):E:= if p:x∈D then f ⟨x,p⟩ else 0
lemma m_eq (f:D→E)(x:D): Maker f x=f x:=dif_pos x.property
namespace SubHol
variable {f g:D→E}
lemma font (p:SubHol D f)(G:ℂ→ E)(h:∀ z:D,G z=f z):Hol D G:=by obtain ⟨F,g,f⟩:=p; exact g.congr fun x hx=> (h ⟨x,hx⟩).trans (f ⟨x,hx⟩).symm
lemma maker (p:SubHol D f):Hol D (Maker f):=p.font _ (m_eq f)
lemma constant (c:E):SubHol D (fun _=>c) :=⟨_,differentiableOn_const (s:=D) c,fun _=>rfl⟩
lemma add (p:SubHol D f)(u:SubHol D g):SubHol D (fun i=> f i+g i):=⟨_,p.maker.add u.maker,fun i=>congrArg₂ (·+·) (m_eq f i) (m_eq g i)⟩
lemma sub (p:SubHol D f)(u:SubHol D g):SubHol D (fun i=> f i-g i):=⟨_,p.maker.sub u.maker,fun i=>congrArg₂ (·-·) (m_eq f i) (m_eq g i)⟩
lemma mul {E:Type*}[NormedRing E][NormedAlgebra ℂ E]{f g:D→E}(p:SubHol D f)(u:SubHol D g):SubHol D (fun i=> f i*g i):=⟨_,p.maker.mul u.maker,fun i=>congrArg₂ (·*·) (m_eq f i) (m_eq g i)⟩
lemma sum {F:X→D→E}(S:Finset X)(p:∀ i∈S,SubHol D (F i)):SubHol D (fun x=>∑ i∈S,F i x):=by induction S using Finset.induction_on with | empty=> simp; exact constant _ | insert i S u ih=> simp_rw [Finset.sum_insert u]; exact (p _ (Finset.mem_insert_self ..)).add (ih fun j s=> p j (Finset.mem_insert_of_mem s))
lemma prod {E:Type*}[NormedCommRing E][NormedAlgebra ℂ E]{F:X→ D→E}(S:Finset X)(p:∀ i∈S,SubHol D (F i)):SubHol D (fun x=>∏ i∈S,F i x):=by
 induction S using Finset.induction_on with
 | empty=> simp; exact constant _
 | insert i S u ih=>simp_rw [Finset.prod_insert u]; exact (p _ (Finset.mem_insert_self ..)).mul (ih fun j s=> p j (Finset.mem_insert_of_mem s))
lemma comp (p:SubHol D f)(K:E→ G)(w:Differentiable ℂ K): SubHol D (K ∘ f):=⟨_,w.comp_differentiableOn p.maker, fun _=> congrArg _ (m_eq _ _)⟩
lemma exp {E:Type*}[NormedCommRing E][NormedAlgebra ℂ E][CompleteSpace E]{f:D→E}(p:SubHol D f):SubHol D (fun i=>NormedSpace.exp (f i)):= p.comp _ fun _=> hasFDerivAt_exp.differentiableAt
lemma linear (p:SubHol D f)[FiniteDimensional ℂ E](L:E→ₗ[ℂ]G):SubHol D (fun z=> L (f z)):=p.comp _ (LinearMap.toContinuousLinearMap L).differentiable
lemma pi [Fintype X]{F:D→X→E} (p:∀ i:X,SubHol D (fun j=>F j i)): SubHol D F:=by
 choose G g w using p; refine ⟨fun u i=> G i u,?_ ,fun z=> funext fun i=> w i z⟩; exact fun i v=>differentiableWithinAt_pi.mpr fun j=> g j i v
lemma sail (p:SubHol D f)(c:ℂ):SubHol D (fun z=>c • f z):=p.comp _ (differentiable_id.const_smul c)
lemma lineL [MeasurableSpace X](μ:Measure X)[IsFiniteMeasure μ]{F:D→X→E}(d:IsOpen D)(h:∀ z: X, SubHol D fun x=>F x z)(p:∀ z:D,Integrable (F z) μ)(v:∀ z:D, ∀ᵐ x∂μ,‖F z x‖ ≤ C) : SubHol D fun z=> ∫ i,F z i∂μ:=by
 let G(u i):= Maker (fun x:D=>F x i) u; have ht(z:D):G z=F z:=funext fun i=>m_eq (fun x:D=>F x i) z
 have hg:Hol D (fun z=>∫ i,G z i∂μ):= cord μ d (fun i=>(h i).maker) (fun z g=>by rw [ht ⟨z,g⟩]; exact p _) (C:=C) (fun z g=>by rw [ht ⟨z,g⟩]; exact v _)
 exact ⟨_,hg,fun z=> by rw [ht z]⟩
end SubHol
end YM.CF.Floral
