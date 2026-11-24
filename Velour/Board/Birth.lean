import Velour.Board.Ramp
/-!
# From Journey Family replication to any torus-marker replication

A package for pricing strategies that buy all disjoint leaves together.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 1200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
open SatinVerification

open Tapestry
variable {Λ: Preparation} {u : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus u)) (H:Real.exp 1 ≤ Λ.x)
 (s i:ℕ)
local notation "K" => tent Y H
local notation "n" => Journey.side Y i s
local notation "m" => momentm Y i s
local notation "Render" => exhibit Y H s i
variable {w:ℕ}{o:Cell}{f:Family (tent Y H)}
 {Key:Type}
 (G:Cell → Key→Prop) (bible:Key→Mark (Journey.side Y i s))
variable
 (base:∃ x,G 0 x ∧ exhibit Y H s i f=bible x)
 (turns:∀ a x,G a x → ∀ (j:Axis)(d:ℤ), 
    ∃ y,G (tipped j d a) y ∧ reflMark j (PaneCut (tent Y H) w o j d) (bible x)=bible y)

lemma renderTumble (j:Axis)(d:ℤ)(T:Tile K):
 Render (tumble w o j d T).leaf=reflMark j (PaneCut K w o j d) (Render T.leaf):=
 displayRef (terrain Y H (Y.ir i) s) _ _ (T.leaf m)

include base turns
lemma changedLeaf
 (T:Tile K) (h:Transit w o f T):
 ∃ x,G T.plot x ∧ Render T.leaf=bible x:=by
 induction h with
 | here=>exact base
 | @turn T h j d ih=>
    obtain ⟨x,a,b⟩:=ih
    obtain ⟨y,c,e⟩:=turns _ _ a j d
    exact ⟨y,c,by rw [renderTumble,b,e]⟩
omit base turns
lemma played_as {l:List (Tile K)} (c:Tile K → Key)
 (h:∀ t∈l, Render t.leaf=bible (c t)):
 Render (Representation l)=((l.map c).map bible).prod:=by
 induction l with
 | nil=> exact actual_one ..
 | cons t l ih=>
   change Render (t.leaf*Representation l) = bible _ * _
   rw [actual_product,h t List.mem_cons_self,ih (fun y r=>h _ (List.mem_cons_of_mem _ r))]
   rfl
include base turns
lemma inscribe {l:List (Tile K)}{L U:Cell}
  (p:Paved w o f l L U)
  (accept:Key→Prop)
  (val:∀a x,G a x → accept x)
  (sep:Key→Key→Prop)
  (different:∀a b, RangeAt L U a→RangeAt L U b→ a≠b→ ∀x y,G a x → G b y → sep x y):
 ∃ labels:List Key, labels.length=l.length ∧ Render (Representation l)=(labels.map bible).prod ∧
  (∀x∈labels,accept x) ∧ labels.Pairwise sep:=by
 haveI:Nonempty Key:=⟨base.choose⟩
 choose! bprice lease using fun t h=> changedLeaf Y H s i G bible base turns t (p.homes t h)

 refine ⟨_,List.length_map bprice,played_as Y H s i bible _ (fun t v=>(lease t v).2),?_,?_⟩
 · intro x h; obtain ⟨t,v,rfl⟩:=List.mem_map.mp h
   exact val _ _ (lease t v).1
 rw [List.pairwise_map]
 exact p.sorted.imp_of_mem fun {x y} v u ne=> different _ _ (p.places x v) (p.places y u) ne _ _ (lease x v).1 (lease y u).1

end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard


