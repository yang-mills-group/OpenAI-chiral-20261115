import MarchC.Era
import YM.SU5.Six.Chambers
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
open Cheer Calico
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(F:ℕ)(C D:ℕ→ℕ→ℝ)(H:Rovers P F C D x)(a:Axis)(j:ℕ)
local notation "Ω" => P.heaven a (P.otherSpectrum 3 a x)
local notation "ξ"=>P.otherSpectrum 3 a x
local notation "V"=> P.ManyF a ξ
local notation "U"=>P.cartage a ξ
local notation "E"=>(P.seasons a ξ).E
local notation "θ"=>crownM P x F C D
noncomputable abbrev mzone := {z:Vantage|∀i:Axis,0< z i}
lemma mze : IsOpen mzone:=by
 apply isOpen_iff_mem_nhds.mpr; intro z p; exact show ∀ᶠ u:Vantage in 𝓝 z,∀ i:Axis,0<u i from Filter.eventually_all.mpr (fun i=>(continuous_apply i).continuousAt.tendsto.eventually (lt_mem_nhds (p i)))
lemma plane_rise(b:ℝ)(y:Vantage)(z:ℝ)(p:b<z)(f g:V)(u v:Vantage):AnalyticAt ℝ (fun t:ℝ=> valley P x a ((Function.update y a t) a - b) (Function.update y a t+u-v) f g) z:=by
 let q:V:= U (y+u-v) g
 have hf:AnalyticAt ℝ (fun t:ℝ=> inner ℂ f (E (t-b).toNNReal q)) z:= (Spine.heat_analytic V a (P.seasons a ξ) f q (z-b) (sub_pos.mpr p)).comp (f:=fun t=>t-b) (analyticAt_id.sub analyticAt_const)
 refine hf.congr (Eventually.of_forall fun t=>?_)
 let w:= Function.update y a t+u-v
 have he:U w=U (y+u-v):= of_slideP x a w (y+u-v) (fun i h=>by simp only [w,Pi.add_apply,Pi.sub_apply,update_of_ne h])
 exact congrArg (inner ℂ f) ((P.warm_drive a ξ _ _ _).trans (congrArg₂ (fun (s:ℝ)(p:(V).Op)=>p (E s.toNNReal g)) (congrArg (·-b) (update_self a t y).symm) he.symm))
variable (y:Vantage)
include J H
lemma loiter : ∀ t:ℝ,update y a t ∈ mzone → AnalyticAt ℝ (fun z:ℝ=> θ (update y a z)) t:=by
 intro t p
 let L:ℕ→ℝ:=fun s=>booth P F s a
 have he:Tendsto L atTop (𝓝 0):=by
    let l:=fun b=> tendsto_pi_nhds.mp (tin_center P F a b) a
    exact add_zero (0:ℝ) ▸ ((l true).add (l false))
 have hp:0<t:=by simpa only [update_self] using p a
 obtain ⟨s,d,ds⟩:= ((he.eventually (gt_mem_nhds hp)).and (eventually_ge_atTop F)).exists
 let v:=centreA P F s a true; let z:=centreA P F s a false; let f:=incoming P x F C D s a true; let g:=incoming P x F C D s a false
 let Pz(z:ℝ):=update y a z
 apply (plane_rise P x a (L s) y t d f g v z).congr
 filter_upwards [lt_mem_nhds d, lt_mem_nhds hp] with b h k
 have h':update y a b ∈ mzone:=by intro i; by_cases q:i=a; subst i; rw [update_self]; exact k; have l:=p i; rw [update_of_ne q] at l ⊢; exact l
 exact (axis_price P x J F C D H a s ds h' (by rw [update_self]; exact h)).symm


-- generic propagation of slices.W
noncomputable abbrev slices (A:Vantage→ℂ):Prop:= ∀ (a:Axis)(y t), update y a t∈mzone→ AnalyticAt ℝ (fun s:ℝ=>A (update y a s)) t
omit J H
lemma slice_alive(A:Vantage→ℂ)(u:slices A)(v:∃p∈mzone,A p≠0) : mzone ⊆ closure {p∈mzone|A p≠0}:=by
 rintro p hp
 apply mem_closure_iff_nhds.mpr
 intro R t
 by_contra f
 obtain ⟨ε,he,hε⟩:= Metric.mem_nhds_iff.mp (show R∩mzone∈𝓝 p from inter_mem t (mze.mem_nhds hp))
 have hx(L:Finset Axis)(z:Vantage)(y:z∈mzone)(hz:∀ j:Axis,j∉L→dist (z j) (p j)<ε): A z=0:= by
    induction L using Finset.induction_on generalizing z with
    | empty=>
      have hu:z∈R:=(hε (Metric.mem_ball.mpr ((dist_pi_lt_iff he).2 (fun j=>hz j (Finset.notMem_empty _))))).1
      by_contra g
      exact f ⟨z,hu,y,g⟩
    | @insert i L hi ih=>
      let B:Set ℝ:= Ioi 0; let G(t:ℝ):= A (update z i t)
      have hw(b:ℝ)(t:b∈B):update z i b∈mzone:=by intro j; by_cases q:j=i; subst j; rw [update_self]; exact t; rw [update_of_ne q]; exact y j
      have gt : G =ᶠ[𝓝 (p i)] 0 := by
        filter_upwards [(Metric.ball_mem_nhds (p i) he), isOpen_Ioi.mem_nhds (show p i ∈ B from hp i)] with b g ht
        apply ih _ (hw _ ht)
        intro j hj; by_cases q:j=i
        · subst j; rw [update_self]; exact g
        rw [update_of_ne q]; exact hz j (by simpa only [Finset.mem_insert,not_or] using And.intro q hj)
      have hg:AnalyticOnNhd ℝ G B:=fun _ v=> u _ _ _ (hw _ v)
      have a₁: EqOn G 0 B:= hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioi _).isPreconnected (hp i) gt
      exact (congrArg A (Function.update_eq_self i z).symm).trans (a₁ (y i))
 obtain ⟨z,p,w⟩:=v; exact w (hx Finset.univ z p (fun _ h=>(h (mem_univ _)).elim))
#print axioms loiter
#print axioms slice_alive
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
