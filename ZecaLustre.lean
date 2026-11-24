import ZecaMemorial
import ZecaTwain
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

open Hierarchy.Seld Hierarchy.Seld.Zeca
local notation "G" => P.ManyF j x
local notation "Ω"=> P.heaven j x
local notation "S"=>P.seasons j x
local notation "E"=> (P.seasons j x).E

open Hierarchy.Seld.Poin

variable {F:P.Nib j x}{Y:ℕ→P.Apron}
lemma Truth.twin {P:Spine}{j:Axis}{x:P.Spectrum0 j}
 {F:P.Nib j x}{D:Zeca.Moment (P.ManyF j x)}
 (h:P.Truth j x F D): P.Truth j x (P.twinNib j x F) D.dagger:=by
 refine ⟨?_⟩
 intro a b p q
 unfold twinNib; rw [h.translation b a q p]
 unfold Zeca.Moment.cost Zeca.Moment.dagger
 rw [star_mul,star_mul,show star _=_ from para_adj (P.seasons j x) D.n a p,
        show star _=_ from para_adj (P.seasons j x) D.n b q,
        mul_assoc]

def Lustre (D:Zeca.Moment G) (Z:ℕ→P.Apron):Prop:=
  P.Bought j x D Z ∧
  P.Bought j x D.dagger (fun i=>(Z i).kiss P j)

lemma gets_lustre (h:P.Iguana j x F Y):
  ∃ D,P.Truth j x F D ∧ P.Lustre j x D Y:=by
 obtain ⟨D,d⟩:=P.bottles_m j x F h.nib.bottle
 exact ⟨D,d,⟨F,h.nib,d⟩,_,h.twin,d.twin⟩

def poseAt (j:Axis) (v:OS.Cross j)(u:ℝ):Vantage:=
 fun i=> if i=j then u else v.val i
lemma posing (j:Axis)(v:OS.Cross j)(u:ℝ):
 poseSp j (poseAt j v u)=v∧ poseAt j v u j=u:=by
 refine ⟨?_,by simp [poseAt]⟩
 unfold poseSp
 apply Eq.trans _ (eyes_toFace ..).symm
 apply congrArg; funext i; exact if_neg i.property

open Boundary
structure Realm :Prop where
 real : RealStamp (P.seasons j x)
 nv_eq (y:E4): M (P.seasons j x) y (nv P j x).val= (nv P j x).val
 dawn {n:ℕ} (D:Fin n→Zeca.Moment (P.ManyF j x)): ∃ C,Marks (P.seasons j x) (nv P j x).val D C
 wick {n:ℕ} (D:Fin n→Zeca.Moment (P.ManyF j x))(g:Fin n→Test4){C}
    (p:Marks (P.seasons j x) (nv P j x).val D C):
    (∀ i:ℕ, Integrable (fun x=> Joint.materialize n g x * C i x Complex.I)) ∧
    Tendsto (fun i:ℕ=>∫ x, Joint.materialize n g x * C i x Complex.I)
       atTop (𝓝 (Wproduct (P.seasons j x) (nv P j x) D g))
 provides (F:P.Nib j x)(Y:ℕ→P.Apron)
    (h:P.Iguana j x F Y): ∃ D,P.Truth j x F D ∧ P.Lustre j x D Y

lemma realm :P.Realm j x:=⟨realStamp _,P.nova j x,fun D=>⟨_,arc_marks ..⟩,
 fun D g _ p=>wick _ _ _ (P.nova j x) g p,fun _ _=> P.gets_lustre j x⟩

lemma any_quote (a:P.Spectrum0 3)(V:P.Ellis 3 a)
 (I:Type) (D:I→Zeca.Moment (P.ManyF j (P.advocate 3 a j)))
 (Z:ℕ→I→P.Apron)(b:∀i,P.Bought j (P.advocate 3 a j) (D i) (fun k=>Z k i))
 (L:List I)(sp:I→OS.Cross j)(t:I→ℝ)
 (o:L.Pairwise fun i k=> t i<t k):
 let p:=fun i=>poseAt j (sp i) (t i)
 Tendsto (fun k=> P.commonWell 3 a (Z k) p L) atTop
     (𝓝 (quoteL (P.seasons j (P.advocate 3 a j)) (P.heaven j (P.advocate 3 a j)) D sp t L)):= by
 intro p
 have c:spY j p=sp:=funext fun i=> (posing ..).1
 have h:(fun i=>p i j)=t:=funext fun i=> (posing ..).2
 rw [←c, ←h]
 exact P.quoteWell j a V D Z p (fun _=>p) _ _ .rfl b
   (fun _=> tendsto_const_nhds) (o.imp (by intro i k q; simpa only [p,poseAt,if_pos] using q))
#print axioms realm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
