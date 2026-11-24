import Velour.Gallery.Showroom
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 110000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe



private lemma seam (l r o:ℝ) (p:l<o)(q:o<r):
 EuOrder [false,true] (fun b=>cond b o l) (fun b=>cond b r o):=by
 constructor
 · intro b _; cases b
   · exact p
   exact q
 · simp
 intro a b s t h
 have v:=(congrArg List.length h)
 simp at v; have u:s=[]:= List.length_eq_zero_iff.mp (by omega)
 subst s
 simp only [List.nil_append,List.cons.injEq] at h
 obtain ⟨rfl,rfl,rfl⟩:=h; rfl

variable (P:Spine)(a:P.Spectrum0 3)(J:P.Ellis 3 a)(j:Axis)
local notation "x"=>P.advocate 3 a j
local notation "Ω"=>P.heaven j x

include J
lemma broadPair (A B:P.Apron)(F G:SampleDose)
 (l o r:ℝ)(u:l<o)(v:o<r)
 (c:∀p∈tsupport F.val,l<p j-A.realWidth P j ∧ p j+A.realWidth P j<o)
 (d:∀p∈tsupport G.val,o<p j-B.realWidth P j ∧ p j+B.realWidth P j<r):
 Tendsto (fun n=>P.singleState j n x (P.prepared n A F*P.prepared n B G))
  atTop (𝓝 (inner ℂ Ω ((P.sleeveEu j x F l o A) ((P.sleeveEu j x G o r B) Ω)))) :=by


 let C (b:Bool):=cond b B A
 have b(i:Bool):
     P.FitsLayout j x (cond i G F) (cond i o l) (cond i r o) 0 (.inr (C i)):= by
   cases i
   · exact c
   exact d
 have g:∀ᶠ n in atTop,∀i∈[false,true],(C i).s≤n:= by
    filter_upwards [eventually_ge_atTop A.s,eventually_ge_atTop B.s] with n p q i hi
    cases i
    · exact p
    exact q
 have t:=P.install_buttons j a [false,true] _ _ _ (fun b=>.inr (C b)) (seam l r o u v) J
   (fun i=>0) (fun i _=>b i) (fun _=>id) id tendsto_id (fun _ _=>tendsto_id) g
 simp only [List.map_cons,List.prod_cons,List.prod_nil,List.map_nil,mul_one] at t
 exact t

#print axioms broadPair
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

