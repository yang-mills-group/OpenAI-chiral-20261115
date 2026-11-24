import YM.SU5.Six.MSplit
import YM.SU5.Relativistic.TrueSeparation
import YM.SU5.Six.PressSmear
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
variable {V U:Finset Cover} {a b:P.Test}
/-!
# Single dressed sensor, even joined to other probes, as witness of charge
at height s. Beam records physically disjoint within-summand pin budgets, not
a single fixed charge pocket for the entire stencil. W indicates the matter
*representation* of a distinguished dressed bilinear in every summand, not
all matter dependence (and is preserved through promotion; see KeepCharge).
-/
def Beam (P:Spine)(s:ℕ)(D:Finset Cover)(W:Bool): Submodule ℂ P.Test:=
 Submodule.span ℂ {x:P.Test | ∃ (S T V U:Finset Cover)(a b:P.Test), S ∪ T ⊆ V ∧ V ⊆ D ∧ U ⊆ D ∧
   Disjoint (P.pinFoot s S) (P.pinFoot s T) ∧ Disjoint (P.pinFoot s V) (P.pinFoot s U) ∧
   a.val∈DressedPair P.calibration W S T V ∧ a∈enclave P.calibration ∧ b∈bay P.calibration U true ∧ x=a*b}

def Apron.Beams (B:P.Apron)(W:Bool):Prop:=B.F ∈ P.Beam B.s B.S W
lemma enterBeam (h:S∪T⊆V)(v:V⊆D)(u:U⊆D)(p: Disjoint (P.pinFoot s S) (P.pinFoot s T))(d:Disjoint (P.pinFoot s V) (P.pinFoot s U))
 (z:a.val∈ DressedPair K W S T V)(c:a∈enclave K)(m:b∈bay K U true) : a*b ∈ P.Beam s D W:=
 Submodule.subset_span (show _∈_ from ⟨S,T,V,U,_,_,h,v,u,p,d,z,c,m,rfl⟩)

lemma Beam.mono (p:D⊆U): P.Beam s D W ≤ P.Beam s U W:=by
 apply Submodule.span_le.mpr; rintro f ⟨S,T,V,R,a,b,x,y,e,h,k,z,c,t,rfl⟩
 exact enterBeam x (y.trans p) (e.trans p) h k z c t
lemma Beam.bay_le : P.Beam s D W ≤ (bay K D true).toSubmodule:=by
 apply Submodule.span_le.mpr; rintro f ⟨S,T,V,R,a,b,x,y,e,h,k,z,c,t,rfl⟩
 exact Subalgebra.mul_mem (bay K D true)
   (tallerBay K V true y ((Tapestry.locates ..).mpr (dressed_test K W S T V x z))) (tallerBay _ _ _ e t)

lemma Beam.sense_mul (h:a ∈P.sensing V s W)(g:b∈bay K U true)(v:V⊆D)(u:U⊆D)(p:Disjoint (P.pinFoot s V) (P.pinFoot s U)):
     a*b∈P.Beam s D W:=by
 let R:=P.Beam s D W
 refine Submodule.span_induction (p:=fun f _=>f*b∈R) (fun f h=>?_) (by rw [zero_mul]; exact R.zero_mem)
    (fun _ _ _ _ x y=>by rw [add_mul]; exact R.add_mem x y) (fun z f _ x=>by rw [smul_mul_assoc]; exact R.smul_mem _ x) h
 obtain ⟨S,T,L,x,y,l,m,j⟩:=h
 exact enterBeam x (y.trans v) u l (p.mono_left (P.pin_mono _ _ _ y)) m j g
lemma sensedDefault (P:Spine)(s:ℕ)(Z:Lead.Clan)(n:ℕ)(h:P.calibration.ℓ<n):
 P.defaultR Z n∈P.sensing (P.flash n).patio s Z.2:=by
 let A:=P.flash n
 change (↑(purePrice Z):ℂ)⁻¹ • (P.frontMat Z n)∈_
 apply Submodule.smul_mem
 exact Submodule.subset_span (show _∈_ from ⟨_,_,A.patio,Finset.union_subset
   (Finset.singleton_subset_iff.mpr (porchBorn A)) (Finset.singleton_subset_iff.mpr (porchGone A)),fun _ h=>h,
     P.pocket_gap s n h,P.front_charge Z n,P.front_real Z n⟩)
lemma Beam.of_sensed (h:a ∈P.sensing D s W) : a∈P.Beam s D W:= by
 rw [←mul_one a]; exact sense_mul h ((bay _ ∅ true).one_mem) (fun _ e=>e) (Finset.empty_subset _) (by simp [pinFoot])
lemma Beam.join (h:a∈P.Beam s D W)(g:b∈bay K T true)(p:Disjoint (P.pinFoot s D) (P.pinFoot s T)):
   a*b∈P.Beam s (D∪T) W:=by
 let R:=P.Beam s (D∪T) W
 refine Submodule.span_induction (p:=fun f _=>f*b∈R) (fun f h=>?_) (by rw [zero_mul]; exact R.zero_mem)
    (fun _ _ _ _ x y=>by rw [add_mul]; exact R.add_mem x y) (fun z f _ x=>by rw [smul_mul_assoc]; exact R.smul_mem _ x) h
 obtain ⟨S,N,V,U,x,y,e,v,u,j,H,z,c,d,rfl⟩:=h
 rw [mul_assoc]
 refine enterBeam e (v.trans Finset.subset_union_left)
   (Finset.union_subset (u.trans Finset.subset_union_left) (Finset.subset_union_right : T⊆D∪T)) j ?_ z c
   (Subalgebra.mul_mem (bay K (U∪T) true) (tallerBay _ _ _ subset_union_left d) (tallerBay _ _ _ subset_union_right g))
 rw [P.pin_union]; exact Set.disjoint_union_right.mpr ⟨H,p.mono_left (P.pin_mono _ _ _ v)⟩

section ward
variable {X:Dome P.calibration→ₗ[ℂ]ℂ}(fct:Factors P.calibration X)(law:MatterWard P.calibration X ∨ GaugeWard P.calibration X)
include fct law
lemma Beam.fee (v:a∈P.Beam s D W): X a=0:= by
 refine Submodule.span_induction (p:=fun f _=>X f=0) (fun f h=>?_) X.map_zero
   (fun _ _ _ _ p q=>by rw [map_add,p,q,add_zero]) (fun z _ _ p=>by rw [map_smul,p,smul_zero]) v
 obtain ⟨S,T,V,U,x,y,e,w,u,p,H,z,c,d,rfl⟩:=h
 exact ward_price K W S T V fct law c z e (P.pin_disjoint _ _ _ p) d (P.pin_disjoint _ _ _ H)
end ward
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
