import YM.SU5.Aria.Personnel
import YM.SU5.Selected.Separable
/-! # Bookkeeping for print with an IR heat buffer. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 800000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "u"=> enclave P.calibration
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E
local notation "m"=> timeMesh P.par
local notation "Q" => P.shifts j
local notation "L"=> P.par.R.L.val
variable {s t v w:ℕ}
/-- A centered or displaced print at physical step-s on width w ticks,
including exact operator purchase at the same elected color.
This level of abstraction hides the dependency on the width. -/
def ThreadOp (s w:ℕ)(f:P.Test)(T:(P.ColorHil j x).Op):Prop :=
 ∃ (a:P.Card j s w)(p:0<w)(h:P.voxTest j s a.val∈ enclave K),
      f=P.voxTest j s a.val ∧ T=Φ (P.door j s w p a h)
variable {P j x}
variable {f g : P.Test}{T U:(P.ColorHil j x).Op}

lemma ThreadOp.unique (q:P.ThreadOp j x s w f T)(r:P.ThreadOp j x s w f U): T=U:= by
 obtain ⟨a,p,h,rfl,rfl⟩:=q; obtain ⟨b,p,h,e,rfl⟩:=r
 have d:a=b:=Subtype.ext (Subtype.ext (congrArg (fun g:P.Test=>g.val) e))
 subst b; rfl


lemma ThreadOp.mono (q:P.ThreadOp j x s w f T)(e:w=v)(d:f=g):
   P.ThreadOp j x s v g T:= e ▸ d ▸ q
lemma ThreadOp.heat (p:0<w) :
    P.ThreadOp j x s w 1 (E (whenly m s w)):=by
 let f:= SlabMark.identity Y₀ H s j false w
 have h:P.Eucl j _=P.atSide j s w p f:= Subtype.ext ((ticket_birth Y₀ H P.law s P.history P.projection.clipped j false (P.room j) w p).symm)
 exact ⟨f,p,show (1:P.Test)∈ u from one_mem _,rfl,
       congrArg (fun z:P.Physical j=>Φ z) (Subtype.ext (a1:=P.risesColor j (whenly m s w)) h)⟩
lemma ThreadOp.cat (q:P.ThreadOp j x s w f T)(r:P.ThreadOp j x s v g U):
   P.ThreadOp j x s (w+v) (f * Q w g) (T * U):=by
 obtain ⟨a,p,h,rfl,rfl⟩:=q; obtain ⟨b,d,hg,rfl,rfl⟩:=r
 let c:= SlabMark.edit Y₀ H s j false w v a b
 have he: (P.voxTest j s a.val)* (Q (w:ℤ) (P.voxTest j s b.val))=P.voxTest j s c.val:=Subtype.ext (editor ..).symm
 have ht: P.voxTest j s c.val∈u:= he ▸ Subalgebra.mul_mem u h (P.shifts_keep j w hg)
 refine ⟨c,add_pos p d,ht,he,?_⟩
 rw [← map_mul]
 exact congrArg _ (Subtype.ext (P.concat ..))


lemma heatVoid: E 0=1 :=by
 change Φ (P.risesColor j 0)=_
 refine (congrArg (fun z:P.Physical j=>Φ z) (Subtype.ext (a2:=(1:P.Physical j)) (P.eucl_zero j))).trans (map_one _)
lemma ThreadOp.bef (q:P.ThreadOp j x s w f T) (n:ℕ):
   P.ThreadOp j x s (n+w) (Q n f) (E (whenly m s n)*T):=by
 rcases n.eq_zero_or_pos with e|e
 · rw [e,Nat.cast_zero,zero_add,P.shifts_zero,when_zero,heatVoid,one_mul]; exact q
 have h:= (ThreadOp.heat e).cat q
 rwa [one_mul] at h
lemma ThreadOp.aft (q:P.ThreadOp j x s w f T) (n:ℕ):
   P.ThreadOp j x s (w+n) f (T*E (whenly m s n)):=by
 rcases n.eq_zero_or_pos with e|e
 · rw [e,add_zero,when_zero,heatVoid,mul_one]; exact q
 have h:= q.cat (ThreadOp.heat e)
 rwa [map_one,mul_one] at h
lemma ThreadOp.pad (q:P.ThreadOp j x s w f T) (n k:ℕ):
   P.ThreadOp j x s (n+w+k) (Q n f) (E (whenly m s n)*T*E (whenly m s k)) := (q.bef n).aft k

lemma ThreadOp.zero(p:0<w) : P.ThreadOp j x s w 0 0:=by
 let a:=P.positiveVox j s ∅ 0 (zero_mem _) (fun x h=>by simp at h)
 let b:P.Card j s w:= ⟨a,∅,InTest.zero,fun x h=>by simp at h⟩
 refine ⟨b,p,show (0:P.Test)∈u from zero_mem _,rfl,?_⟩
 have h:(P.door j s w p b (show (0:P.Test)∈u from zero_mem _))=0:=
   Subtype.ext (Subtype.ext (P.box_zero j s w p b rfl))
 rw [h,map_zero]

private lemma linear_alpha {A:Type*} [CStarAlgebra A]{Z:Hilbert}
    (f:A →⋆ₐ[ℂ] Z.Op)(z:ℂ)(e t k:A)(p:z • e + t=k):
    z • f e + f t=f k:= by rw [←map_smul, ← map_add,p]

lemma ThreadOp.lin (q:P.ThreadOp j x s w f T)(r:P.ThreadOp j x s w g U)(z:ℂ):
    P.ThreadOp j x s w (z • f + g) (z • T + U):=by
 obtain ⟨a,p,h,rfl,rfl⟩:=q; obtain ⟨b,_,h',rfl,rfl⟩:=r
 obtain ⟨D,v,e⟩:=a.property; obtain ⟨B,d,e'⟩:=b.property
 let g:= z • P.voxTest j s a.val + P.voxTest j s b.val
 have hd: g∈ bay K (D∪B) true:= InTest.add (InTest.smul z (InTest.mono v Finset.subset_union_left)) (InTest.mono d Finset.subset_union_right)
 have he: Between K j 0 (ruler P.par.block * w) (D∪B):=by intro y k; rcases Finset.mem_union.mp k with u'|u'; exact e y u'; exact e' y u'
 let c:P.Card j s w:=
    ⟨P.positiveVox j s _ g hd (fun y t=>(he y t).1),_, hd,he⟩
 have i:P.voxTest j s c.val∈u:= (u).add_mem ((u).smul_mem h z) h'
 refine ⟨c,p,i,rfl,?_⟩
 exact linear_alpha (Z:=X) Φ _ _ _ _ (Subtype.ext (Subtype.ext (P.box_linear j s w p a b c z rfl).symm))


lemma ThreadOp.pos (q:P.ThreadOp j x s w f T): 0<w:= q.choose_spec.choose
lemma ThreadOp.smul (q:P.ThreadOp j x s w f T)(z:ℂ):
    P.ThreadOp j x s w (z • f) (z • T):=by
 have h:= q.lin (ThreadOp.zero q.pos) z
 rwa [add_zero,add_zero] at h
lemma ThreadOp.add (q:P.ThreadOp j x s w f T)(r:P.ThreadOp j x s w g U):
    P.ThreadOp j x s w (f + g) (T + U):=by
 have h:= q.lin r 1
 rwa [one_smul,one_smul] at h
lemma ThreadOp.sub (q:P.ThreadOp j x s w f T)(r:P.ThreadOp j x s w g U):
    P.ThreadOp j x s w (f-g) (T-U):=by
 have h:=q.add (r.smul (-1))
 rwa [neg_smul,one_smul,←sub_eq_add_neg,neg_smul,one_smul,←sub_eq_add_neg] at h


lemma ThreadOp.sum {ι:Type*}{F:ι→P.Test}{V:ι→ (P.ColorHil j x).Op}
    (p:0<w)(D:Finset ι)(q:∀i∈D,P.ThreadOp j x s w (F i) (V i)):
    P.ThreadOp j x s w (∑i∈D,F i) (∑i∈D,V i):=by
 induction D using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact ThreadOp.zero p
 | @insert i D h t=> simp only [sum_insert h]; exact (q i (mem_insert_self ..)).add (t fun d k=>q d (mem_insert_of_mem k))
lemma ThreadOp.higher (q:P.ThreadOp j x s w f T) (h:s≤t):
   P.ThreadOp j x t (L^(t-s)*w) (P.conveying s (t-s) f) T:=by
 obtain ⟨a,p,e,rfl,rfl⟩:=q
 refine ⟨_,_,P.refine_keeps _ _ e _,(P.convey_vox j a h),congrArg _ (Subtype.ext (P.upper_tab j s w p a t h))⟩
lemma Apron.sewn (D:P.Apron):
    P.ThreadOp j x D.s (D.u j + D.u j)
      (Q (D.u j) D.F) (D.engine P j x):=
 ⟨D.cardB P j,add_pos (D.pos j) (D.pos j),D.color P j,rfl,rfl⟩


lemma Apron.promoted (D:P.Apron)(h:D.s≤t):
    P.ThreadOp j x t (D.zoom P t j+D.zoom P t j)
        (Q (D.zoom P t j) (D.full P t)) (D.engine P j x):=by
 obtain ⟨a,q,r⟩:=D.full_realizes P j t h
 exact ⟨a,_,show _∈u from q ▸ P.shifts_keep j _ (D.fullColor P t),
     q.symm,congrArg (fun z:P.Physical j=>Φ z) (Subtype.ext r)⟩
lemma Apron.shiftCap (D:P.Apron)(h:D.s≤t)(p:Cover):
    P.ThreadOp j x t (D.zoom P t j+D.zoom P t j)
        (Q ((D.zoom P t j:ℤ)-p j) (P.chartAll p (D.full P t)))
        (P.charter j x (P.vtile t p) (D.engine P j x)):=by
 obtain ⟨a,d,f,k⟩:=D.transported P j x t h p
 exact ⟨a,_,d,f.symm,k⟩
-- for same level rather than promote, use cruise transverse directly
lemma ThreadOp.shiftCap (q:P.ThreadOp j x s w f T)(p:Cover):
   P.ThreadOp j x s w (Q (-(p j)) (P.chartAll p f)) (P.charter j x (P.vtile s p) T):=by
 obtain ⟨a,d,f',rfl,rfl⟩:=q
 rw [P.chart_transverse,P.shifts_sum,neg_add_cancel,P.shifts_zero]
 obtain ⟨b,e,r,h⟩:=P.door_move_list j x s w d (look j) p a f'
 exact ⟨b,d,e,r.symm,P.released_truck j x (P.vtile s p) _ _ _ rfl h⟩


lemma Apron.capHere (D:P.Apron) (p:Cover):
    P.ThreadOp j x D.s (D.u j+D.u j)
        (Q ((D.u j:ℤ)-p j) (P.chartAll p D.F))
        (P.charter j x (P.vtile D.s p) (D.engine P j x)):=by
 unfold chartAll
 exact ((D.sewn (x:=x)).shiftCap p).mono rfl (by unfold chartAll; rw [P.cruise_mesh,P.shifts_sum,neg_add_eq_sub])

lemma ThreadOp.expected (q:P.ThreadOp j x s w f T):
   inner ℂ ω (T ω)=P.singleState j s x f:=by
 obtain ⟨a,p,e,rfl,rfl⟩:=q; rw [P.attended,P.view_scalar]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

