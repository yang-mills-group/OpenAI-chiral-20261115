import MarchC.Shirts
import MarchC.Veneer
import MarchC.Item
import Acacia.Tan
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open _root_.YM.Preen _root_.Acacia _root_.Yoland YM.OS Cheer
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(H:Rovers P F C D x)
local notation "Q"=> crownM P x F C D
local notation "ξ" a:max=>P.otherSpectrum 3 a x
local notation "U" a:max=>P.cartage a (P.otherSpectrum 3 a x)
local notation "E" a:max=>(P.seasons a (P.otherSpectrum 3 a x)).E
local notation "L" a:max=>P.seasons a (P.otherSpectrum 3 a x)
local notation "X" a:max=>P.ManyF a (P.otherSpectrum 3 a x)
local notation "A" j:max a:max=>centreA P F j a true
local notation "B" j:max a:max=>centreA P F j a false
local notation "o" j:max a:max=>incoming P x F C D j a
variable (a:Axis)(y:Vantage)(p:y∈mzone)
noncomputable def roverZ(a:Axis)(y:Vantage)(r:ℝ):Vantage:= update y a (y a+r)
lemma rover₀ : roverZ a y 0=y:=by unfold roverZ; rw [add_zero,Function.update_eq_self]
lemma zinctravel (p r:Vantage)(b:ℝ): (U a) (roverZ a y b+p-r)=(U a) (y+p-r) := of_slideP x a _ _ (fun i h=> by rw [Pi.sub_apply,Pi.add_apply,roverZ, update_of_ne h]; rfl)
lemma rover_exchange(b:Axis)(h:a≠b)(r t:ℝ):roverZ b (roverZ a y r) t=roverZ a (roverZ b y t) r:=by
 funext i; by_cases p:i=a
 · subst i; simp [roverZ,Function.update_self,Function.update_of_ne h]
 by_cases u:i=b
 · subst i; simp only [roverZ,update_self,update_of_ne h.symm]
 simp only [roverZ,update_of_ne p,update_of_ne u]
include p in
lemma belong (r:ℝ)(h':0<y a+r): roverZ a y r∈mzone:=by intro i; unfold roverZ; by_cases h:i=a; subst i; rw [update_self]; exact h'; rw [update_of_ne h]; exact p i
include J H
lemma rope (j:ℕ)(r:ℝ)(h:F ≤ j)(hu:booth P F j a<y a+r)(hp:roverZ a y r∈ mzone): Q (roverZ a y r)=
 inner ℂ ((o j a) true) ((U a) (y+A j a-B j a) (dawn (L a) ((y a-booth P F j a)+r) ((o j a) false))):=by
 let z:=roverZ a y r; have he:z a=y a+r:= update_self ..
 exact (axis_price P x J F C D H a j h hp (hu.trans_eq he.symm)).trans (congrArg₂ (fun (i:Vantage)(t:ℝ)=>valley P x a t i ((o j a) true) ((o j a) false)) (rfl) (show z a-booth P F j a=y a-booth P F j a+r from (by rw [he]; abel)) |>.trans (congrArg (fun  (T:(X a).Op)=> inner ℂ ((o j a) true) (T ((E a) _ ((o j a) false)))) (zinctravel P x a y (A j a) (B j a) r))) -- metavars
noncomputable def ored (y:Vantage)(n:ℕ):ℂ:= iteratedDeriv n (fun t:ℝ=> Q (roverZ 3 y t)) 0
private lemma keep_arg(j:ℕ)(g:F ≤ j)(k:ℝ)(hk:0<k)(u:a≠3)(n:ℕ):
 let v:=y a-booth P F j a; let w:= y 3-booth P F j 3
 0<v→0<w→ (∀{r s:ℝ},|r|≤k→ -k<s → v+r>0∧ w+s>0 ∧ roverZ 3 (roverZ a y r) s∈ mzone) → AnalyticAt ℝ (fun r:ℝ=>ored P x F C D (roverZ a y r) n) 0:=by
 intro v w hv hw hc
 let F₁(s:ℝ):= (U a) (roverZ 3 y s+A j a-B j a); let F₂(r:ℝ):= (U 3) (roverZ a y r+A j 3-B j 3)
 let K(r s:ℝ):= Q (roverZ 3 (roverZ a y r) s)
 change AnalyticAt ℝ (fun r:ℝ=>iteratedDeriv n (K r) 0) 0
 refine _root_.Acacia.hall (L a) (L 3) k hk K F₁ F₂ ((o j a) true) ((o j a) false) ((o j 3) true) ((o j 3) false) v w hv hw (fun s=>P.cart_pay ..) (fun r=>P.cart_pay ..) ?_ ?_ n
 · intro r s hR hS
   have z:0<v+r:=(hc hR hS).1; have hx:=(hc hR hS).2.2; have hi:=rover_exchange a y 3 u r s; have hx':roverZ a (roverZ 3 y s) r ∈ mzone:= hi ▸ hx; have he: roverZ 3 y s a=y a:=update_of_ne u ..
   let t(y:ℝ):ℂ:= inner ℂ ((o j a) true) (F₁ s (dawn (L a) ((y-booth P F j a)+r) ((o j a) false)))
   exact (congrArg (Q) hi).trans ((rope P x J F C D H a (roverZ 3 y s) j r g (by rw [he]; unfold v at z; linarith only [z]) hx').trans (congrArg t he))
 intro r s hR hS; have z:0<w+s:=(hc hR hS).2.1; have hx:=(hc hR hS).2.2; have he:roverZ a y r (3:Axis)=y 3:=update_of_ne (Ne.symm u) ..
 let t(y:ℝ):ℂ:= inner ℂ ((o j 3) true) (F₂ r (dawn (L 3) ((y-booth P F j 3)+s) ((o j 3) false)))
 exact (rope P x J F C D H 3 (roverZ a y r) j s g (by rw [he]; unfold w at z; linarith only [z]) hx).trans (congrArg t he)
include p
set_option maxHeartbeats 1150000 in
lemma keep_analytic (u:a≠3)(n:ℕ):AnalyticAt ℝ (fun r:ℝ=> ored P x F C D (roverZ a y r) n) 0:=by
 have he(b:Axis):Tendsto (fun j:ℕ=>booth P F j b) atTop (𝓝 0):=by let l:=fun c=> tendsto_pi_nhds.mp (tin_center P F b c) b; exact add_zero (0:ℝ) ▸ ((l true).add (l false))
 obtain ⟨j,g,ht,hs⟩:= ((eventually_ge_atTop F).and (((he a).eventually (gt_mem_nhds (p a))).and ((he 3).eventually (gt_mem_nhds (p 3))))).exists
 let v:= y a-booth P F j a; let w:=y 3-booth P F j 3
 have hv:0<v:=sub_pos.mpr ht; have hw:0<w:=sub_pos.mpr hs
 let k:= min v (min w (min (y a) (y 3)))/2; have hk:0<k:=half_pos (lt_min hv (lt_min hw (lt_min (p a) (p 3))))
 have ha:2*k ≤ v:=by unfold k; linarith only [min_le_left v (min w (min (y a) (y 3)))]
 have hq:2*k ≤ min w (min (y a) (y 3)):=by unfold k; linarith only [min_le_right v (min w (min (y a) (y 3)))]
 have hc{r s:ℝ}(hR:|r| ≤ k)(hS:-k<s): v+r>0∧ w+s>0 ∧ (roverZ 3 (roverZ a y r) s)∈mzone :=by
    have hx:0< v+r:= by linarith only [ha,hk,(abs_le.mp hR).1]
    have hy:0<w+s:=by linarith only [hq,min_le_left w (min (y a) (y 3)),hS,hk]
    refine ⟨hx,hy,belong 3 _ (belong a y p r ?_) s ?_⟩
    · linarith only [hq,(abs_le.mp hR).1,(min_le_left (y a) (y 3)),min_le_right w (min (y a) (y 3)),hk]
    unfold roverZ; rw [update_of_ne (Ne.symm u)]
    linarith only [hq,hS,(min_le_right (y a) (y 3)),min_le_right w (min (y a) (y 3)),hk]
 exact keep_arg P x J F C D H a y j g k hk u n hv hw hc
#print axioms keep_analytic
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
