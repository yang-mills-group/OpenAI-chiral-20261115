import Ridgetop.Agenda
import SatinPhantom
import Ridgetop.Angles
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "T" d:max=> stackW d
local notation "τy" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
local notation "A*" d:max=> ((girder P d):ℝ)
local notation "H*" d:max w:max=> outlookT P d w
open CF.Onyx
open CF.Ember (pinch)
open Ridgetop
-- reject Gaussian langs – exact!
theorem gauntlet : ¬ Languish P:=by
 rintro ⟨l,F,h⟩
 have hv:∀ᶠ d:ℕ in atTop,∃ (w:Cover)(i:ℕ), Enrolled P d (stairW d) w∧
    needleL P d w*CF.Ember.pinch (showF P (T d) i) ≤ flowε d ∧ ‖docket P (T d) i (outlookT P d w)‖*(A* d)^8 ≤ collector P d:=by
   filter_upwards [h,F] with d e v
   obtain ⟨w,he,H⟩:=e; rw [boon_empty] at H
   obtain ⟨i,a,b⟩:= coupons P l d w v.1 (by simpa only [zero_pow (by norm_num:(2:ℕ)≠0),sub_zero,badge] using H (by simp))
   exact ⟨w,i,he,a,b⟩
 obtain ⟨D,x,H⟩:= extraction_of_frequently_atTop hv.frequently
 choose W i E a b using H
 let S(n:ℕ):=showF P (T (D n)) (i n); let X(n:ℕ):=needleL P (D n) (W n)
 have Tw:Tendsto (fun n=> X n* CF.Ember.pinch (S n)) atTop (𝓝 0):= squeeze_zero (f:=fun n=>X n*CF.Ember.pinch (S n)) (fun n=> mul_nonneg (needle_pos P W E n).le (CF.Ember.pinch_pos _).le) a (summers.comp x.tendsto_atTop)
 have Tn:Yard S X:= ⟨needle_pos P W E,goWaist P x.tendsto_atTop W E,Tw,fun n=>evenShow P (T (D n)) (i n)⟩
 let y(n:ℕ):=outlookT P (D n) (W n)
 have hT:=sewer P x.tendsto_atTop W E
 let lB(n):=P.run.uv (P.cutoff (P.projection.columns (i n)))-T (D n); let V₀:=P.par.V; let K:=P.par.K; let B₀(n):=V₀.L.H (lB n)
 let t(n):=docket P (T (D n)) (i n) (y n)
 have hZ:Tendsto (fun n=>(X n:ℂ)^8*t n) atTop (𝓝 Ridgetop.visible):= pulseLimit Tn hT (fun n=>(V₀.L.roof (lB n)).1) K.width (zero_lt_one.trans_le V₀.up) (fun n=>(V₀.L.roof (lB n)).2.1 (S n))
 let yL:ℝ:=4*(pollN P:ℝ)+2; have hy:0 ≤ yL:=by unfold yL; positivity
 have he:Tendsto (fun n=> (X n)^8 *‖t n‖) atTop (𝓝 ‖Ridgetop.visible‖):=by
    apply hZ.norm.congr; intro n; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (needle_pos P W E n)]
 have ha:Tendsto (fun n=> (X n)^8*‖t n‖) atTop (𝓝 0):= by
    have A:Tendsto (fun n=>yL^ (8:ℕ)*collector P (D n)) atTop (𝓝 0):=by simpa only [Function.comp_def,mul_zero] using ((dollar_flow P).comp x.tendsto_atTop).const_mul (yL^8)
    refine squeeze_zero (fun _=>mul_nonneg (by positivity) (norm_nonneg _)) ?_ A
    intro n; have hN:=(needle_span P (E n)).2; change X n ≤ yL*(A* (D n)) at hN -- hN pair
    have hq:=pow_le_pow_left₀ (needle_pos P W E n).le hN 8
    change (X n)^8 *‖t n‖ ≤ _; rw [mul_pow] at hq
    refine (mul_le_mul_of_nonneg_right hq (norm_nonneg _)).trans ?_
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [mul_comm]; exact b n
 exact Ridgetop.visibility (norm_eq_zero.mp (tendsto_nhds_unique he ha))
#print axioms gauntlet
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
