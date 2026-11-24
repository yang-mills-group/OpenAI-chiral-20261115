import Preen.Licensed
import Preen.Scene
import Preen.Vise
import Preen.Gamma
import Preen.FoyerX
import Preen.Weights
import Risa.Engage
import Preen.Spurt
import Risa.SeedBox
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
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "K"=>P.calibration
local notation "V"=>P.run.meter.a s
local notation "Yx"=> hat P.par.R.L P.par.x s
local notation "θ"=>scaleY (Yx)
local notation "σ"=>sock A (Yx)
local notation "I"=>Fin (cardD P A s)
local notation "Nc" i:max=> count P.run s i
local notation "Y"=>P.run
local notation "π₀" i:max => P.period (P.projection.rows i)
local notation "ζ₀" i:max => P.cutoff (P.projection.columns i)
open _root_.YM.Preen Calico _root_.YM.Gleam.Luster Almanac
open Ballad Cordial Cheer Prototype Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn Designs Twah Six Habitat Habitat.Hemlock
variable (x:P.Spectrum0 3)
noncomputable abbrev boonW (P:Spine)(d:ℕ)(L H:ℕ)(w:Cover):ℝ:= (pilot P (stackW d) (drive L H) (deputize P d w) false).price
noncomputable abbrev roomsW (P:Spine)(d:ℕ)(L H:ℕ)(w:Cover):ℝ:= (pilot P (stackW d) (drive L H) (outlookT P d w) true).price
local notation "g" d:max=> (((girder P d):ℕ):ℝ)
local notation "bq" l:max d:max w:max=> boonW P d l (8*l+6) w
local notation "β" l:max d:max w:max=> roomsW P d l (8*l+6) w
local notation "YQ" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
private lemma accounting{u a r:ℝ}(x y:ℂ)(a' b:ℝ)(h:1≤ u)(l:ℕ)(p:r ≤ u^l)(v:0≤ r)(t:‖x-(a':ℂ)‖*u^(8*l+6)≤1)(ht:‖y-(b:ℂ)‖*u^(8*l+6)≤1)(g':|b|≤1)(e:r^8*‖x-star y*y‖≤a): |a'- b^2| *r^8 ≤ a +4/u:=by
 have hu:0<u:=zero_lt_one.trans_le h
 have hr(k:ℕ):1 ≤ u^k:=one_le_pow₀ h
 have hv:=lt_of_lt_of_le zero_lt_one (hr 6)
 have hR:r^8 ≤ u^(8*l):=(pow_le_pow_left₀ v p 8).trans_eq (by rw [←pow_mul,Nat.mul_comm])
 have hP: r^8*u ≤ u^(8*l+6):=by rw [pow_add]; refine mul_le_mul hR ?_ hu.le (by positivity); simpa only [pow_one] using pow_le_pow_right₀ h (show 1≤6 by norm_num)
 have wh(d:ℝ)(h:0≤d)(p:d*u^(8*l+6)≤1): r^8*d ≤ 1/u:=by rw [le_div_iff₀ hu]; nlinarith only [mul_le_mul_of_nonneg_left hP h,p]
 have hY:‖y-(b:ℂ)‖≤1:=(le_mul_of_one_le_right (norm_nonneg _) (hr _)).trans ht
 let v':=‖x-(a':ℂ)‖; let t':= ‖y-(b:ℂ)‖
 have hz: ‖y‖≤ 2:=by
    have hx:‖(b:ℂ)‖ ≤1:=(by simpa only [Complex.norm_real,Real.norm_eq_abs] using g') -- rw via simpa
    apply (norm_le_norm_sub_add y (b:ℂ)).trans; linarith only [hY,hx]
 have hi: ‖star y*y-((b:ℂ)^2)‖≤ t'*3:=by
    have hw:star (b:ℂ)=(b:ℂ):=Complex.conj_ofReal _
    rw [show star y*y-((b:ℂ)^2)=(star (y-(b:ℂ)))*y+ (b:ℂ)*(y-(b:ℂ)) from (by rw [star_sub,hw]; ring)]
    refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_star,norm_mul,Complex.norm_real,Real.norm_eq_abs]; unfold t'; nlinarith only [mul_le_mul_of_nonneg_left hz (norm_nonneg (y-(b:ℂ))),mul_le_mul_of_nonneg_right g' (norm_nonneg (y-(b:ℂ)))]
 have h0: |a'-b^2|≤ v'+ ‖x-star y*y‖+t'*3:=by
    rw [← Real.norm_eq_abs,← Complex.norm_real,Complex.ofReal_sub,Complex.ofReal_pow]
    rw [show (a':ℂ)-(b:ℂ)^ (2:ℕ)=( (a':ℂ)-x+(x-star y*y))+(star y*y-(b:ℂ)^ (2:ℕ)) from (by ring)]
    exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (le_of_eq (by unfold v'; rw [norm_sub_rev (a':ℂ)]))) hi)
 have hp:=wh _ (norm_nonneg _) t; have ht':=wh _ (norm_nonneg _) ht
 change _*v'≤_ at hp; change _*t' ≤ _ at ht'
 apply (mul_le_mul_of_nonneg_right h0 (by positivity)).trans; have hb:4/u=4*(1/u):=by ring
 rw [hb]; linarith only [hp,ht',e]
variable (M:Py.Rate.Pitching.Focus.Morn P.par.K)(t:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(J:P.Ellis 3 x) {K':P.Register} {c r:ℕ→ℕ}(B:P.Experiment K' c r x J)
variable (m:∀ s:ℕ,F ≤ s→Accordance P M F s (C s) (D s))(p:RobeRoad P F C D x)(q:Jones P M t F C D x)(e:Enviro P x)
include B m p q e
/-- from any alternative 2 reach failing free shelves on tournament. -/
lemma banquet {L:ℕ}(k:SpanPrice P L)(h:¬Vacation P F C D x B): ∀ᶠ d:ℕ in atTop, ∃ w:Cover, Enrolled P d (stairW d) w ∧ (|bq L d w|≤1 → |β L d w-(bq L d w)^2| *(g d)^8 ≤ (shoreH d)⁻¹+4/(YQ d)):=by
 filter_upwards [vanished P F C D x M m p t q B h,k,e L (8*L+6),feeRatio P] with d p ht j hf
 obtain ⟨w,r,v⟩:=p
 refine ⟨w,r,fun l=>?_⟩
 rw [estateT P x w d hf.1] at v
 exact accounting _ _ _ _ (Gleam.Luster.Risa.summitT _) L ht.1 (Nat.cast_nonneg _) (j _ true ((ht.2 w r).1)) (j _ false ((ht.2 w r).2)) l v
omit p m q e B
lemma fades : Tendsto (fun d=> (shoreH d)⁻¹ +4/(YQ d)) atTop (𝓝 0):=by
 have hv:Tendsto (fun d=> (YQ d)) atTop atTop:=Gleam.Luster.Risa.summitG.comp (turnover P.par|>.comp (tendsto_atTop_mono (show hikeV ≤ stackW from fun _=>Nat.le_add_right ..) goes_town))
 have h':Tendsto (fun d=> ((shoreH d)⁻¹)) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp shore_up
 have p:= h'.add ((tendsto_inv_atTop_zero.comp hv).const_mul 4)
 simpa [div_eq_mul_inv,Function.comp_def] using p
#print axioms banquet
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
