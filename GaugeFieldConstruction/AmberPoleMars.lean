import GaugeFieldConstruction.SimaBoltR
import Mathlib.Analysis.Complex.Liouville
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
section poles
variable {J:Hilbert}{j:Axis}(A:OS.Semigroup J j)(v:J)
structure VignMars (J:Hilbert) where
    lo:ℝ
    hi:ℝ
    pay:J.Op
noncomputable def ActorMars (p:Option ℝ)(l:List (VignMars J)) :J:= match l with
 | []=>v
 | i::s=> A.E ((p.map (fun b=>(i.lo-b).toNNReal)).getD 0) (i.pay (ActorMars (some i.hi) s))
def ReflectActorMars (b:VignMars J): VignMars J:= ⟨-b.hi,-b.lo,b.pay.adjoint⟩
abbrev AheadActorMars (b:ℝ)(L:List (VignMars J)):=∀ i∈ L,b ≤ i.lo
abbrev OrderActorMars (L:List (VignMars J)) := L.Pairwise (fun i j=>i.hi ≤ j.lo)
variable (p:∀ t,A.E t v=v)
local notation "P_Σ"=> ActorMars A v
lemma MirrorHeatMars (t:ℝ≥0)(x y:J): inner ℂ (A.E t x) y=inner ℂ x (A.E t y):=by nth_rw 1 [← A.sym]; exact ContinuousLinearMap.adjoint_inner_left _ _ _
include p
lemma LedgeActMars (L:List (VignMars J))(t r:ℝ)(h:AheadActorMars r L)(q:t≤r): P_Σ (some t) L=A.E ((r-t).toNNReal) (P_Σ (some r) L):=by
 cases L with
 | nil => exact (p _).symm
 | cons i l=>
    rw [ActorMars,ActorMars]; change A.E (i.lo-t).toNNReal _=A.E _ (A.E ((i.lo-r).toNNReal) _); rw [show (i.lo-t)=(r-t)+(i.lo-r) from by ring,Real.toNNReal_add (sub_nonneg.mpr q) (sub_nonneg.mpr (h i (List.mem_cons_self ..))),A.time]; rfl
lemma CueActorMars (L:List (VignMars J))(t:ℝ): inner ℂ v (P_Σ none L)=inner ℂ v (P_Σ (some t) L):=by
 cases L with
 | nil=>rfl
 | cons i l=>
    rw[ActorMars,ActorMars]; simp only [Option.map_none, Option.getD_none,Option.map_some,Option.getD_some,← MirrorHeatMars,p]
lemma FoldActorMars (L R:List (VignMars J))(u:ℝ)(he: AheadActorMars u L)(hv:AheadActorMars (-u) R)(hO:OrderActorMars L) (h:∀ i∈ L,i.lo ≤ i.hi): inner ℂ v (P_Σ none (L.reverse.map ReflectActorMars ++R)) = inner ℂ (P_Σ (some u) L) (P_Σ (some (-u)) R):=by
 induction L generalizing R u with
 | nil=> exact CueActorMars A v p R _
 | cons i L ih=>
    let r:= i.lo; let t:= i.hi
    have hp:u≤r:=he i (List.mem_cons_self ..); have hx:r≤t:=h _ (List.mem_cons_self ..)
    obtain ⟨Q,H⟩:= List.pairwise_cons.mp hO
    let W:= ReflectActorMars i :: R
    have hV: AheadActorMars (-t) W :=by
        intro j e; rcases List.mem_cons.mp e with rfl|k
        · exact le_rfl
        exact (neg_le_neg (hp.trans hx)).trans (hv j k)
    have hS:OrderActorMars L:=H
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append]
    rw [ih W t Q hV hS (fun k p=> h _ (List.mem_cons_of_mem _ p)),show P_Σ (some (-t)) W=A.E ((-t- -t).toNNReal) (i.pay.adjoint (P_Σ (some (-r)) R)) from rfl,sub_self,Real.toNNReal_zero,A.eZero,ContinuousLinearMap.id_apply]
    rw [LedgeActMars A v p R (-r) (-u) hv (neg_le_neg hp), show -u- -r=r-u from by ring]; change inner ℂ _ (i.pay.adjoint _) = inner ℂ (A.E (r-u).toNNReal (i.pay _)) _; rw [MirrorHeatMars]; exact ContinuousLinearMap.adjoint_inner_right _ _ _
#print axioms FoldActorMars
end poles
variable {cost:ℕ→P.Test→ℂ}{j:Axis}(C:Porch P cost j)
local notation "η"=>C.DegreeHab
local notation "Ζ"=>C.BrightHab
local notation "Ξ"=>C.groundHab
local notation "T" p:max=> (Ζ).E p
local notation "U" v:max=> (Ζ).U (diameter v)
abbrev LadderRackMars (k:P.Slabs j): C.DegreeHab.Op:=(C.canopy.track.aviator C.canopy.list).orthogonalProjectionOnto ∘L C.ρ k ∘L (C.canopy.track.aviator C.canopy.list).subtypeL
lemma LadderRackUpMars (k:P.Slabs j): LadderRackMars C (Star.star k)=(LadderRackMars C k).adjoint:=by unfold LadderRackMars; rw [map_star]; erw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp, (C.canopy.track.aviator C.canopy.list).adjoint_subtypeL,(C.canopy.track.aviator C.canopy.list).adjoint_orthogonalProjectionOnto]; rfl
-- sun-preservation. At operator level (real-locale). X φ
lemma SpireHTMars (t:ℝ≥0): C.BrightHab.E t C.groundHab= Ξ:= Subtype.ext ((congrArg (fun X:C.H.Op=>X C.Ω) (C.heat t)).trans (C.still t)) -- tune
noncomputable abbrev StampActMars (x:Axis→ℝ)(k:P.Slabs j): C.DegreeHab.Op:= ((U x)*(LadderRackMars C k))*(U (-x))
abbrev TrolleyMars (x:Axis→ℝ)(k:P.Slabs j)(a:ℝ): VignMars C.DegreeHab:= ⟨x j-a,x j+a,StampActMars C x k⟩
noncomputable abbrev flipTactMars (j:Axis)(x:Axis→ℝ):= Function.update x j (- x j)
lemma LoopζMars (x:Axis→ℝ)(t u:C.DegreeHab): inner ℂ ((U x) t) u=inner ℂ t ((U (-x)) u):=by
 have he:(U x) ((U (-x)) u)=u:=by
    rw[← ContinuousLinearMap.comp_apply,← (Ζ).space,← diamond_add,add_neg_cancel,diamond_zero,(Ζ).uZero,ContinuousLinearMap.id_apply]
 nth_rw 1 [←he]; exact LinearIsometry.inner_map_map (𝕜:=ℂ) (show η →ₗᵢ[ℂ] η from { (U x).toLinearMap with norm_map':=(Ζ).unitary _}) _ _
lemma TickBackMars (x:Axis→ℝ): ((U x) : C.DegreeHab.Op).adjoint= U (-x):=by apply ContinuousLinearMap.ext; intro v; apply ext_inner_left ℂ; intro y; rw[ContinuousLinearMap.adjoint_inner_right]; exact LoopζMars C x y v
lemma diameterFlipMars (x:Axis→ℝ)(j:Axis): diameter (a:=j) (flipTactMars j x)=diameter x:=by
 apply Subtype.ext; ext1 y; by_cases p:y=j
 · subst y; exact (diameter _).2.trans (diameter _).2.symm
 exact (diameter_at _ y p).trans ((Function.update_of_ne p ..).trans (diameter_at _ y p).symm)
lemma LoopActMars (x:Axis→ℝ)(k:P.Slabs j)(a:ℝ): TrolleyMars C (flipTactMars j x) (Star.star k) a= ReflectActorMars (TrolleyMars C x k a):=by
 let Y:= C.BrightHab
 have hp(z:Axis→ℝ): diameter (a:=j) (-z)= -diameter z:=by unfold diameter; exact map_neg ..
 have he:diameter (a:=j) (- flipTactMars j x)=diameter (-x):=by rw[hp,hp,diameterFlipMars]
 simp only [ReflectActorMars,TrolleyMars,Function.update_self,StampActMars, LadderRackUpMars] -- tune
 rw [diameterFlipMars,he]
 congr 1
 · ring
 · ring
 change _= Star.star ((U x)*LadderRackMars C k*(U (-x))); rw[star_mul,star_mul]; change _=((U (-x)) : C.DegreeHab.Op).adjoint*((LadderRackMars C k).adjoint*((U x) : C.DegreeHab.Op).adjoint); rw [TickBackMars, TickBackMars,neg_neg,mul_assoc]
variable {I:Type}[Fintype I][DecidableEq I](σ:I→PermWallJ P)(V:I→ P.Slabs j)(x:I→Axis→ℝ)
def billActMars (L:List I):= L.map (fun i=> TrolleyMars C (x i) (V i) (StallJ P (σ i)))
abbrev StriddenMars (i:I)(b:Option ℝ)(w:Axis→ℝ): C.DegreeHab.Op:=(StageR σ C V).gliding b i w
lemma WagonMars (b:Option ℝ)(L:List I): (show C.DegreeHab from (StageR σ C V).roadList L x b)= ActorMars C.BrightHab C.groundHab b (billActMars C σ V x L):=by
 induction L generalizing b with
 | nil=>rfl
 | cons i l ih=>
    rw [billActMars,List.map_cons,ActorMars,roadList]; let a:=StallJ P (σ i); let v:= x i j+a; rw [show (StageR σ C V).endline (x i) i=v from ?_]; swap; · change x i j-a+(a+a)=v; unfold v; ring
    exact Eq.trans ((show _=_ from congrArg (fun u:C.DegreeHab => (StriddenMars C σ V i b (x i)) u) (ih (some v)))) (by cases b <;> rfl)
lemma EarningActorMars (L:List I): Repertoire.reading (StageR σ C V) L x= inner ℂ C.groundHab (ActorMars C.BrightHab C.groundHab none (billActMars C σ V x L)):=by exact congrArg (inner ℂ C.groundHab) (WagonMars ..)
#print axioms EarningActorMars
#print axioms LoopActMars
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
