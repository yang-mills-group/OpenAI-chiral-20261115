import ZecaSnap
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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

variable (s w:ℕ)(a b:ℝ)
local notation "β"=> bell (timeMesh P.par)
-- capacity at center, physical pads
def Vat (F:P.Test)(T:(P.ManyF j x).Op):Prop:=
 ∃ U, P.Snap j x s (2*w) (P.shifts j w F) U ∧
         P.buff j x (a- β s w) (b-β s w) U=T
namespace Vat
variable {P j x s w a b} {F Z:P.Test}{B T:(P.ManyF j x).Op}(h:P.Vat j x s w a b F T)
include h
lemma unique (q:P.Vat j x s w a b F B):T=B:=by
 obtain ⟨u,h,rfl⟩:=h; obtain ⟨t,g,rfl⟩:=q; rw [h.unique g]
lemma add (q:P.Vat j x s w a b Z B): P.Vat j x s w a b (F+Z) (T+B):=by
 obtain ⟨u,h,rfl⟩:=h; obtain ⟨t,g,rfl⟩:=q
 unfold Vat; rw [map_add]; exact ⟨_,h.add g,map_add ..⟩
lemma sub (q:P.Vat j x s w a b Z B): P.Vat j x s w a b (F-Z) (T-B):=by
 obtain ⟨u,h,rfl⟩:=h; obtain ⟨t,g,rfl⟩:=q
 unfold Vat; rw [map_sub]; exact ⟨_,h.sub g,map_sub ..⟩
lemma smul (z:ℂ): P.Vat j x s w a b (z•F) (z•T):= by
 obtain ⟨u,h,rfl⟩:=h; unfold Vat; rw [map_smul]; exact ⟨_,h.smul z,map_smul ..⟩
omit h
lemma zero (c:0<w):P.Vat j x s w a b 0 0:=by
 unfold Vat; rw [map_zero]
 exact ⟨0,⟨0,Fired.zero (by omega),map_zero _⟩,map_zero _⟩
lemma sum {I:Type*}(c:0<w)(A:Finset I)(F:I→P.Test) (T:I→(P.ManyF j x).Op)
   (p:∀ i∈A,P.Vat j x s w a b (F i) (T i)):
 P.Vat j x s w a b (∑ i∈A,F i) (∑ i∈A,T i):=by
 induction A using Finset.induction with
 | empty=> simpa only [sum_empty] using (zero (s:=s) (a:=a) (b:=b) (x:=x) c)
 | @insert u A v ih =>
    rw [sum_insert v,sum_insert v]
    exact (p u (mem_insert_self ..)).add (ih (fun y v=> p y (mem_insert_of_mem v)))
end Vat
variable (D:P.Apron)
namespace Apron
lemma vat {n:ℤ}(p:D.s=s)
 (i:(D.u j:ℤ)≤w+n)
 (o:n+D.u j ≤ w)
 (u:β s w ≤ a)
 (v:β s w ≤ b):
 P.Vat j x s w a b (P.shifts j n D.F)
    (P.ruby j x D 0 (a+β s n) (b-β s n)):=by
 subst s; let h:=β D.s w; let d:=β D.s n
 let l:=h+d; let r:=h-d
 have e:D.realWidth P j ≤ l:=by unfold realWidth l h d; rw [←bell_add,bell_le];exact i
 have f:D.realWidth P j ≤ r:=by
    unfold r realWidth d h; rw [le_sub_iff_add_le,←bell_add,bell_le];omega
 unfold Vat; rw [P.shifts_sum]
 refine ⟨P.ruby j x D 0 l r,
       D.snap_here P j x i (by omega) (bell_add ..) ?_,
       P.ruby_large j x D _ _ (show a-h+l=a+d by unfold l; ring) (show r+(b-h)=b-d by unfold r; ring)
       (sub_nonneg.mpr u) (sub_nonneg.mpr v) e f _⟩
 rw [show l+r = β D.s w + β D.s w by unfold l r h; ring,←bell_add]
 congr 1; omega
lemma pureVat (p:D.s=s)
 (i:D.u j≤w) (u:β s w≤a)(v:β s w≤b):
 P.Vat j x s w a b D.F (P.ruby j x D 0 a b):= by
 simpa only [P.shifts_zero,bell,Int.cast_zero,zero_mul,sub_zero,add_zero] using
        D.vat P j x s w a b (n:=0) p (by omega) (by omega) u v
end Apron
