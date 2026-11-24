import Minnow.RoverI
import Acacia.Loom
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
open Calico Cheer _root_.Yoland _root_.Acacia
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(H:Rovers P F C D x)
local notation "Q"=>crownM P x F C D
local notation "R" y:max n:max=>ored P x F C D y n
include H J
/-- Every pure time coefficient is separately analytic in all coordinates. -/
lemma aligned (a:Axis)(v:Vantage)(p:ℝ)(n:ℕ)(h:update v a p∈mzone): AnalyticAt ℝ (fun t:ℝ=> R (update v a t) n) p:=by
 let y:=update v a p
 by_cases ha:a=(3:Axis)
 · subst a
   let g(t:ℝ):=Q (update v 3 t)
   have he: AnalyticAt ℝ (iteratedDeriv n g) p:= filter_n n (loiter P x J F C D H _ v _ h) -- helper
   refine he.congr (Eventually.of_forall fun i=>?_); let w :=update v (3:Axis) i
   have h(r:ℝ):roverZ 3 w r=update v 3 (i+r):=by
    funext a; by_cases hx:a=3
    · subst a; simp [roverZ,w]
    simp only [roverZ,w,update_of_ne hx]
   change iteratedDeriv n g i=iteratedDeriv n (fun z=>Q (roverZ 3 w z)) 0
   exact (show iteratedDeriv n g i=iteratedDeriv n (fun r:ℝ=>g (i+r)) 0 from by simp only [iteratedDeriv_comp_const_add,add_zero]).trans (congrArg (fun f:ℝ→ℂ=>iteratedDeriv n f 0) (funext fun r=> (congrArg Q (h r)).symm))
 let f(r:ℝ):= R (roverZ a y r) n
 have he:=keep_analytic P x J F C D H a y h ha n
 refine ((show AnalyticAt ℝ f (p-p) from sub_self p |>.symm ▸ he).comp (f:=fun t:ℝ=> t-p) (analyticAt_id.sub analyticAt_const)).congr (Eventually.of_forall fun i=>?_)
 apply congrArg (fun (z:Vantage)=>R z n) (show roverZ a y (i-p)=update v a i from ?_)
 funext j; unfold y roverZ; by_cases h:a=j
 · subst j; simp only [update_self]; abel
 simp only [update_of_ne (Ne.symm h)]
where filter_n(n:ℕ){f:ℝ→ℂ}{x:ℝ}(h:AnalyticAt ℝ f x): AnalyticAt ℝ (iteratedDeriv n f) x:=by induction n with|zero=>simpa using h|succ n ih=>rw [iteratedDeriv_succ]; exact ih.deriv
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 ξ
local notation "d" j:max=>tidal P F j
local notation "U"=>P.cartage 3 ξ
local notation "S"=>P.seasons 3 ξ
lemma layered (y:Vantage)(p:y∈mzone)(j:ℕ)(h:F ≤ j)(v:W)(E:Aloft.PeriodS P F C D x j v)(w:2*d j<y 3)(n:ℕ): R y n= inner ℂ v (U y (_root_.Yoland.pay (S) n (y 3-(d j+d j)) v)):=by
 let t:= y 3-(d j+d j); have hp:0<t:=by unfold t; linarith only [w]
 let f(i:ℝ):=Q (roverZ 3 y i)
 have he:f=ᶠ[𝓝 0] (fun i:ℝ=> inner ℂ v (U y (dawn (S) (t+i) v))):=by
    filter_upwards [lt_mem_nhds (neg_lt_zero.mpr hp)] with r hr
    have hf:2*d j< (roverZ 3 y r) 3:=by unfold roverZ; rw [update_self]; unfold t at hr; linarith only [hr]
    have hq:roverZ 3 y r∈mzone:=belong _ y p r (by linarith only [tide_price P F j,(show roverZ 3 y r 3=y 3+r from update_self ..) ▸ hf])
    exact (thanks P x J F C D H j h v E (roverZ 3 y r) hq hf).trans (congrArg₂ (fun (b:ℝ)(T:(W).Op)=>inner ℂ v (T (dawn (S) b v))) (show roverZ 3 y r 3 - (d j+d j)= t+r from by unfold roverZ t; rw [update_self]; abel) (show U (roverZ 3 y r)= U y from of_slideP x 3 _ _ (fun i g=>update_of_ne g ..)))
 exact _root_.Acacia.esteem (S) f n v v (U y) t hp he
#print axioms aligned
#print axioms layered
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
