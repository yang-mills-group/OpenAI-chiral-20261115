import YM.SU5.Assay.LeftYarn
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
variable {c:Option Bool}{a b x y:P.Test}
/-! Billing book. Authorship primitives: scalar tuft, single fibre; close by
sums, scales, posing **at the native height**, kisses, and distributive
cross-print on joining a spectator. No algorithmic efficiency intended.
-/
abbrev Folio (P:Spine):=List P.JointPiece
variable {l n:P.Folio}
namespace Folio
variable (l n)
def ink (z:ℂ):P.Folio:= l.map (fun a=>(z•a.1,a.2))
def transcribe (u:P.Test → P.Test):P.Folio:= l.map (fun a=> (u a.1,u a.2))
def crossPrint :P.Folio:= l.flatMap (fun a=> n.map (fun b=>(a.1*b.1,a.2*b.2)))
end Folio
variable (P) in
def Wove (c:Option Bool)(S:Finset Cover)(x:P.Test)(l:P.Folio): Prop:=
 x= (l.map (fun i=>i.1*i.2)).sum ∧ ∀ i∈l,P.Fibre c S i.1 i.2
namespace Wove
lemma prepared' (p:P.Wove (some W) D x l):Presented K W D x l:= ⟨p.1,fun _ h=>(p.2 _ h).prior⟩
lemma aperture (p:P.Wove c D x l) : x∈bay K D false:=by
 obtain ⟨rfl,e⟩:=p
 induction l with
 | nil=> exact (bay ..).zero_mem
 | cons i l h=>
   have u:=e i List.mem_cons_self
   exact (bay ..).add_mem ((bay ..).mul_mem u.glass.part u.park) (h (fun j v=>e j (List.mem_cons_of_mem i v)))
lemma void' (p:P.Wove c D x l):P.Wove none D x l:= ⟨p.1,fun _ h=>(p.2 _ h).void'⟩
lemma mono (q:D⊆S)(p:P.Wove c D x l): P.Wove c S x l:= ⟨p.1,fun _ h=>(p.2 _ h).mono q⟩
lemma fibre (p:P.Fibre c D a b): P.Wove c D (a*b) [(a,b)]:= ⟨by simp,by simpa using p⟩
lemma tuft (h:P.Yarn D x): P.Wove none D x [(x,1)]:= by
 simpa using fibre (Fibre.tuft h)
lemma zilch : P.Wove c D 0 []:=⟨by simp,by simp⟩
lemma staple (p:P.Wove c D x l)(h:P.Wove c D y n):P.Wove c D (x+y) (l++n):=
 ⟨by simp [p.1,h.1],fun i v=>Or.elim (List.mem_append.mp v) (p.2 i) (h.2 i)⟩
section
variable {I:Type*}(b:I→P.Test)(t:I→P.Folio)
lemma stapleList (v:List I)(p:∀ i∈v,P.Wove c D (b i) (t i)):P.Wove c D (v.map b).sum (v.flatMap t):=by
 induction v with
 | nil=> exact zilch
 | cons a v h=>rw [List.map_cons,List.sum_cons,List.flatMap_cons]; exact staple (p a List.mem_cons_self) (h (fun _ u=>p _ (List.mem_cons_of_mem _ u)))
lemma stapleMore (V:Finset I)(p:∀ i∈V,P.Wove c D (b i) (t i)):P.Wove c D (∑i∈V,b i) (V.toList.flatMap t):=by
 have h:=List.sum_toFinset b (V.nodup_toList); rw [Finset.toList_toFinset] at h; rw [h]
 exact stapleList b t _ (fun _ u=>p _ (Finset.mem_toList.mp u))
end
-- `m` can be semilinear, not necessarily an algebra homomorphism
lemma reword (p:P.Wove c D x l)(m:P.Test → P.Test)(k:P.JointPiece→P.JointPiece)(e:m 0=0)(h:∀x y,m (x+y)=m x+m y)
 (u:∀i:P.JointPiece,m (i.1*i.2)=(k i).1*(k i).2)
 (z:∀i:P.JointPiece,P.Fibre c D i.1 i.2→P.Fibre c S (k i).1 (k i).2) : P.Wove c S (m x) (l.map k):=by
 refine ⟨?_,?_⟩
 · obtain ⟨rfl,-⟩:=p
   induction l with
   | nil=>exact e
   | cons i l t=>simp only [List.map_cons,List.sum_cons,h,t,u]
 rintro i v; obtain ⟨j,w,rfl⟩:=List.mem_map.mp v; exact z j (p.2 j w)
lemma smul (p:P.Wove c D x l)(z:ℂ):P.Wove c D (z•x) (l.ink z):=
 reword p (z•·) (fun i=>(z•i.1,i.2)) (smul_zero z) (smul_add z) (fun _=> (smul_mul_assoc ..).symm) (fun _ h=>h.smul _)
lemma left (p:P.Wove c D x l)(i:Axis):P.Wove c (reflectedBox i 0 D) (P.reflectTest i x) (l.transcribe (P.reflectTest i)):=
 reword p _ _ (map_zero _) (map_add _) (fun _=>Subtype.ext (mirror_times ..)) (fun _ h=>h.left ..)
lemma slide (p:P.Wove c D x l)(i:Axis)(z:ℤ):P.Wove c (plow K i z D) (P.shifts i z x) (l.transcribe (P.shifts i z)):=
 reword p _ _ (map_zero _) (map_add _) (fun _=>map_mul ..) (fun _ h=>h.slide ..)
lemma joint (h:P.Wove c S x l)(p:P.Wove none T y n)(d:Disjoint S T):P.Wove c (S∪T) (x*y) (l.crossPrint n):=by
 let v(i:P.JointPiece):=i.1*i.2
 let t(i j:P.JointPiece):P.JointPiece:= (i.1*j.1,i.2*j.2)
 refine ⟨?_,?_⟩
 · obtain ⟨rfl,-⟩:=h; obtain ⟨rfl,-⟩:=p
   have e(i):(v i)*(n.map v).sum=((n.map (t i)).map v).sum:= by
     induction n with
     | nil=>simp
     | cons b n h=>simp only [List.map_cons,List.sum_cons,mul_add,h]; congr 1; exact mul_mul_mul_comm ..
   change (l.map v).sum*(n.map v).sum= ((l.flatMap (fun i=>n.map (t i))).map v).sum
   induction l with
   | nil=>simp
   | cons i l h=>simp only [List.map_cons,List.sum_cons,add_mul,h,e,List.flatMap_cons,List.map_append,List.sum_append]
 intro i u; unfold Folio.crossPrint at u
 obtain ⟨a,j,w⟩:=List.mem_flatMap.mp u
 obtain ⟨b,z,rfl⟩:=List.mem_map.mp w
 exact (h.2 a j).joint (p.2 b z) d
end Wove
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
