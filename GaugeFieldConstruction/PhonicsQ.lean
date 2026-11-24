import GaugeFieldConstruction.Barrera4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona
variable {I J:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]{n:Side}
variable (e:I↪J)(σ:I→Seat n)(σ':J→Seat n)
open Same4
-- no geometry change only label. sum/support.Apply theorem for every singleton newly opened. structural reaches
abbrev PaintEV {T:Type}(k:Finset I × T): Finset J × T:=⟨k.1.image e,k.2⟩
lemma ev_inj (T:Type):Injective (PaintEV (T:=T) e):=by
 rintro ⟨x,y⟩ ⟨v,w⟩ E'; obtain ⟨a,b⟩:=Prod.mk.inj E'; rw [←map_eq_image,←map_eq_image] at a; exact Prod.ext (Finset.map_injective e a) b
lemma ev_surj {T:Type}(u:Finset I)(p:Finset J×T)(h:p.1⊆ u.image e):∃ Q, PaintEV e Q=p:=by
 let A:= (u.filter fun i=> e i ∈ p.1)
 have he:A.image e=p.1:=by
   ext i; constructor
   · intro v; obtain ⟨i,v',rfl⟩:=mem_image.mp v; exact (mem_filter.mp v').2
   intro v; obtain ⟨k,t,rfl⟩:= mem_image.mp (h v); exact mem_image.mpr ⟨k,mem_filter.mpr ⟨t,v⟩,rfl⟩
 exact ⟨(A,p.2),Prod.ext he rfl⟩
local notation "Δ"=> PaintEV e
variable (t t':ℕ)(p:Hub n)
lemma coat (A:Fin t→ PI I n): (Δ∘ A)∈LeadQ p.val.2 (Dusk J n) t ↔ A∈LeadQ p.val.2 (Dusk I n) t:=by
 simp only[LeadQ,mem_filter,mem_univ,true_and]; unfold clouds; simp only[mem_filter,mem_univ,true_and]; rfl
-- general transcript lengths equal.Proof via subst

def iκQ (a:t=t'): Heart p (Dusk I n) t↪ Heart p (Dusk J n) t' where
 toFun i:= ⟨fun j=>PaintEV e (i.val (Fin.cast a.symm j)),by subst t'; exact (coat e _ _ _).2 i.property⟩
 inj' :=by subst t'; intro x y v; exact Subtype.ext (funext fun i=> ev_inj e (Hub n) (congrFun (congrArg Subtype.val v) i))
variable (a:t=t')
include e
lemma anchorQ (b:Heart p (Dusk I n) t): Legist p (Dusk J n) t' (iκQ e t t' p a b)= Legist p (Dusk I n) t b:=by subst t'; rfl
lemma surjC {X:Finset I}(A:Heart p (Dusk J n) t')(v:∀ i:Fin t',(A.val i).1⊆ X.image e): A∈ Set.range (iκQ e t t' p a):=by
 subst t'; choose C g using fun i=> ev_surj e _ _ (v i)
 have he:A.val= PaintEV e∘ C:= funext fun i=>(g i).symm
 let c:Heart p (Dusk I n) t:= ⟨C,(coat e _ p C).1 (by rw[←he]; exact A.property)⟩
 exact ⟨c,Subtype.ext (show _=A.val from he.symm)⟩
abbrev iκF (A:Finset (KI I n)):=A.image (PaintEV e)
lemma plusQ (b: Bool)(A:Finset (KI I n)): BasisI (Flak J n) p b (A.image (PaintEV e))↔ BasisI (Flak I n) p b A:=by
 have hz:til (Flak J n) (A.image (PaintEV e))=til (Flak I n) A:=by unfold til; rw[image_biUnion]
 refine ⟨fun x=> ⟨fun i h j p v=> x.packed (mem_image_of_mem _ h) (mem_image_of_mem _ p) ((ev_inj e _).ne v),fun i v=>x.busy _ (mem_image_of_mem _ v),image_nonempty.mp x.inhab,hz ▸ x.meeting⟩,fun x=>⟨?_,?_, image_nonempty.mpr x.inhab,hz ▸ x.meeting⟩⟩
 · intro i h j u p; obtain ⟨i,h',rfl⟩:=mem_image.mp (show i∈ _ from h); obtain ⟨j,u',rfl⟩:=mem_image.mp (show j∈ _ from u); exact x.packed h' u' (fun e=>p (congrArg _ e))
 intro i h; obtain ⟨i,h',rfl⟩:=mem_image.mp h; exact x.busy _ h'
def iρQ (b b':Bool)(c:b=b')(P: Hub n)(v:p=P): Base (Flak I n) p b ↪ Base (Flak J n) P b' where
 toFun A:= ⟨A.val.image (PaintEV e), v ▸ c ▸ ((plusQ _ _ _ _).2 A.property)⟩
 inj' :=fun A B w=> Subtype.ext (show A.val=B.val from Finset.map_injective (Embedding.mk (PaintEV e) (ev_inj e _)) (by rw [map_eq_image,map_eq_image]; exact congrArg Subtype.val w))
variable (b b':Bool)(c:b=b')(P: Hub n)(x:p=P)
local notation "η"=> iρQ e p b b' c P x
lemma portQ (A:Base (Flak I n) p b): let B:= iρQ e p b b' c P x A; roost (Flak J n) P b' B= roost (Flak I n) p b A ∧ til (Flak J n) B.val=til (Flak I n) A.val:=by
 subst P; subst b'; let A':=iρQ e p b b rfl p rfl A; have v:til (Flak J n) A'.val=til (Flak I n) A.val:=by unfold til; change (Finset.image (PaintEV e) _).biUnion _=_; rw[image_biUnion]
 refine ⟨Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl ?_)) v),v⟩
 change p.val.2∪walls (Flak J n) (A.val.image (PaintEV e)) = p.val.2∪walls (Flak I n) A.val; unfold walls; rw[image_biUnion]
lemma surjH {X:Finset I}(A:Base (Flak J n) P b')(g:∀ i∈A.val,i.1⊆X.image e): A∈Set.range (iρQ e p b b' c P x):=by
 subst P; subst b'; let S:=(univ: Finset (KI I n)).filter fun i=> PaintEV e i∈A.val
 have he:S.image (PaintEV e)=A.val:=by ext i; constructor; rintro t; obtain ⟨x,v,rfl⟩:= mem_image.mp t; exact (mem_filter.mp v).2; intro t; obtain ⟨x,rfl⟩:=ev_surj e _ _ (g _ t); exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,t⟩,rfl⟩
 refine ⟨⟨S,(plusQ e _ _ _).1 (he ▸ A.property)⟩,Subtype.ext he⟩
#print axioms surjH
end Iona
end YM.CF.Scree.Ing
end
