import YM.SU5.FiniteGaugeData.Marked.Variation.Linoleum
import Mathlib.Data.Set.Finite.List
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Finite shelves of Borel functions

Some branch operations need not be continuous functions of their gauge inputs.
Here `shelf` really holds FINITELY MANY possible *functions* of the gauge test
pair. From shelf and **additional** measurability and compact range obtain Deal.
When a shelf of numeric outputs consists of finite-range functions, we can even
locate values EXACTLY by a finite Borel question set.
-/
variable {I J X V Y:Type*}
def Shelf (f:I→X→Y):Prop:= (Set.range f).Finite
namespace Shelf
variable {f:I→X→Y}
protected lemma photo (f:I→ J)(g:J→X→Y)[Finite J]: Shelf (fun i=>g (f i)) := (Set.finite_range g).subset (Set.range_comp_subset_range ..)
protected lemma clear (v:X→Y): Shelf (fun _:I=> v):= Shelf.photo (fun _=>Unit.unit) fun _=> v
protected lemma thenDo (a:Shelf f)(F:(X→Y) → (X→V)) : Shelf (fun i=>F (f i)):= (a.image F).subset (by rintro _ ⟨i,rfl⟩; exact ⟨_,Set.mem_range_self i,rfl⟩)
protected lemma twain {g:I→X→V}{U:Type*}(a:Shelf f)(b:Shelf g)(F:(X→Y)→(X→V)→(X→U)) : Shelf (fun i=> F (f i) (g i)):= ((a.prod b).image (uncurry F)).subset (by rintro _ ⟨i,rfl⟩; exact ⟨(f i,g i),⟨Set.mem_range_self _,Set.mem_range_self _⟩,rfl⟩)
protected lemma merge [Finite J](g:J→I→X→Y)(q:∀ j,Shelf (g j))(z:I→J) : Shelf (fun i=> g (z i) i):=(Set.finite_iUnion q).subset (by rintro _ ⟨i,rfl⟩; exact Set.mem_iUnion.mpr ⟨z i,Set.mem_range_self i⟩)
protected lemma regroup {g:J→I}(h:Shelf f):Shelf (f∘g):= h.subset (Set.range_comp_subset_range ..)
protected lemma swap {g:I→X→Y}(h:Shelf f)(a:∀ i x,f i x=g i x): Shelf g:= (funext fun i=>funext (a i)) ▸ h
protected lemma tuple [Finite J]{g:I→ X→ J→Y} (h:∀ j,Shelf fun i x=> g i x j): Shelf g := by
  have e(j:J):(Set.range (fun i x=> g i x j)).Finite:=h j
  refine ((Set.Finite.pi' e).image (fun f:J→X→Y=>flip f)).subset ?_
  rintro _ ⟨i,rfl⟩; exact ⟨flip (g i), fun j=>(show _∈Set.range _ from ⟨i,rfl⟩), rfl⟩

protected lemma slight [MeasurableSpace X] [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (h:Shelf f)(p:∀ i,Measurable (f i)):Deal f := by
  haveI x:=h.fintype
  apply Deal.assembly (g:=fun (v:Set.range f) (_:I)=> v.val) (X:=X) (T:=fun (_:I)=> Y) _ (fun i=> (⟨f i, Set.mem_range_self _⟩:Set.range f))
  rintro ⟨v,i,rfl⟩; exact deal_of_one (p _) isCompact_univ (fun _=>Set.mem_univ _)
protected lemma exactDeck [MeasurableSpace X][MeasurableSpace Y][MeasurableSingletonClass Y] (h:Shelf f)(p:∀ i,Measurable (f i))(u:∀ i,(Set.range (f i)).Finite) : ∃ P:Deck X, P.dark ∧ ∀ x y,P.withZ x y→∀ i,f i x=f i y:=by
  let V:= Set.range f
  letI:= h.fintype
  choose a z using fun i:↥V=> i.property
  let S(i:↥V):Finset (Set X):= (u (a i)).toFinset.image (fun x=> f (a i) ⁻¹' ({x}:Set Y))
  refine ⟨univ.biUnion S,?_,?_⟩
  · intro F l; obtain ⟨i,_,v⟩:=mem_biUnion.mp l; obtain ⟨x,q,rfl⟩:= mem_image.mp v; exact p _ (measurableSet_singleton _)
  intro x y e i; let j:↥V:= ⟨_, Set.mem_range_self (f:=f) i⟩
  have hx : f (a j) y=f (a j) x:=(e (f (a j) ⁻¹' {f (a j) x}) (mem_biUnion.mpr ⟨j,mem_univ _,mem_image.mpr ⟨_,(u (a j)).mem_toFinset.mpr (Set.mem_range_self x),rfl⟩⟩)).1 (show f (a j) x=f (a j) x from rfl)
  rw [show f i=f (a j) from (z j).symm]; exact hx.symm
end Shelf

variable (S:Finset Cover)(N:I→Side)(Y':X→LinksC)(e:(i:I)→ Edge (Seat (N i)))
lemma graftShelf : Shelf fun i x=> graft S (N i) (Y' x) (e i):=by
  let p(i:I):Prop:= ∃ b:S,pole S (N i) b=(e i).1
  let a(i:I): Option (↥S × Axis):= if h:p i then some (Classical.choose h,(e i).2) else none
  refine Shelf.swap (Shelf.photo a (fun (v:Option (↥S×Axis)) (x:X)=> v.elim (1:SU.E) (fun w=> Y' x (w.1.val,w.2)))) ?_
  intro i x; by_cases h:p i
  · rw [Satin.graft,dif_pos h]; unfold a; rw [dif_pos h]; rfl
  rw [Satin.graft,dif_neg h]; unfold a; rw [dif_neg h]; rfl

local instance : Finite Lattice.Step := Finite.of_injective (fun x:Lattice.Step=> (x.dir,x.neg)) (by rintro ⟨x,g⟩ ⟨y,f⟩ h; cases Prod.mk.inj h; congr)
private lemma journeyShelf (U:(i:I)→ X→Pane (N i))(p:∀ b:(i:I)→Edge (Seat (N i)), Shelf fun i x=> U i x (b i))
    (a:(i:I)→ Seat (N i)) (w:Lattice.Walk): Shelf fun i x=> Lattice.travel (U i x) (a i) w:=by
  induction w generalizing a with
  | nil=> exact Shelf.clear (I:=I) (fun _:X=> (1:SU.E))
  | cons k l ih =>
    let f(i:I)(x:X):SU.E:= k.read (U i x) (a i)
    have hf:Shelf f:= (p fun i=> k.used (a i)).thenDo (fun y x=> if k.neg then (y x)⁻¹ else y x)
    exact hf.twain (ih (fun i=>a i + k.vec)) fun y z x=> y x*z x
lemma travelShelf (U:(i:I)→ X→Pane (N i))(p:∀ b:(i:I)→Edge (Seat (N i)), Shelf fun i x=> U i x (b i))
    (a:(i:I)→ Seat (N i)) (w:I→ Lattice.Walk)(k:ℕ)(h:∀ i,(w i).length≤ k): Shelf fun i x=> travel (U i x) (a i) (w i):= by
  haveI:= (List.finite_length_le Lattice.Step k).fintype
  exact Shelf.merge (J:= ↑{l:List Lattice.Step|l.length≤k}) (fun v i x=> travel (U i x) (a i) v.val) (fun v=> journeyShelf N U p a v.val) (fun i=>⟨w i,h i⟩)
end YM.CF.Buffered.Afterglow.Tapestry
