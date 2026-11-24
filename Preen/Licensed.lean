import Preen.Contest
import Preen.Powley
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
variable (x:P.Spectrum0 3) (w:Cover)
local notation "φ" n:max=>scaleY (hat P.par.R.L P.par.x (stackW n))
local notation "g" d:max=>girder P d
lemma chip {d:ℕ}(p:Enrolled P d (stairW d) w) (i:Axis): ((g d):ℕ)≥(pollN P)∧(-(g d:ℤ)) ≤ nodeC w i ∧ nodeC w i ≤ g d :=by
 have h: pollN P ≤ g d :=by unfold girder trailerH; omega
 refine ⟨h,?_⟩; by_cases t:i=3
 · subst i; let T:=P.par.R.L.val^(stairW d)*reachQ P (hikeV d); have he:(T:ℤ) = (P.par.R.L.val:ℤ)^ (stairW d) *(reachQ P (hikeV d):ℤ):=by unfold T; push_cast; rfl
   obtain ⟨l,r⟩:=p.clock; rw [←he] at r; have hS:T≤ g d:=by unfold T girder trailerH; omega
   constructor<;> omega
 obtain ⟨l,r⟩:=p.side i t; rw [←poll_correct] at r; constructor<;> omega
lemma spin_k {d:ℕ}(i:Axis): 0≤ spindle P d (stairW d) i ∧ spindle P d (stairW d) i ≤((4*g d:ℕ):ℤ):=by
 unfold spindle girder idleCar trailerH; split <;> constructor <;> omega
lemma crews {d:ℕ}(p:Enrolled P d (stairW d) w)(i:Axis): withinT (outlookT P d w) ((4*pollN P+1)*g d) ∧ withinT (deputize P d w) ((4*pollN P+1)*g d):=by
 have hz:0≤(pollN P:ℤ):=by positivity
 constructor; all_goals intro b j; have hl:=chip P w p j; let X:=(g d:ℤ); let K':ℤ:=pollN P; change _ ∧ -X ≤ nodeC w j ∧ _ ≤ X at hl
 · obtain ⟨hp,h⟩:=spin_k (P:=P) (d:=d) j; rw [Int.natCast_mul] at h
   cases b <;> (unfold outlookT; dsimp only; rw [cruise_price])
   · rw [Pi.zero_apply,mul_zero,add_zero,fling_price]; have hK: g d ≤ (4*pollN P+1)*g d:= le_mul_of_one_le_left (by positivity) (by omega); unfold X at hl; split <;> constructor<;> omega
   push_cast only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]; change -((4*K'+1)*X) ≤ nodeC w j+K'*_ ∧ _ ≤ ((4*K'+1)*X)
   have hg:0 ≤ X:=by unfold X; positivity
   change spindle P d (stairW d) j ≤ (4:ℤ)*X at h -- tune
   change 0≤ K' at hz; change _ ∧ nodeC w j + K'* spindle P d (stairW d) j ≤ _; constructor<;> nlinarith only [mul_le_mul_of_nonneg_left h hz, mul_nonneg hz hp,hl.2.1,hl.2.2,mul_nonneg hz hg]
 · have hK:g d ≤ (4*pollN P+1)*g d:=le_mul_of_one_le_left (by positivity) (by omega); unfold deputize; unfold X at hl; omega
/- `authorized A₀`: supply extent certificate w for all Enrolled.L -/
def SpanPrice(L:ℕ):Prop := ∀ᶠ d:ℕ in atTop, (g d:ℝ) ≤ (φ d)^L∧ (∀ w:Cover, Enrolled P d (stairW d) w→ withinT (outlookT P d w) (intervalZ (stackW d) L P) ∧ withinT (deputize P d w) (intervalZ (stackW d) L P)) -- stale notation g φ uses P✝. avoid
lemma span_price:∃ l:ℕ,SpanPrice P l :=by
 obtain ⟨u,h⟩:= measuring_gauge P
 refine ⟨u+1,?_⟩
 have hs:Tendsto (fun i=> φ i) atTop atTop:= Gleam.Luster.Risa.summitG.comp (turnover P.par|>.comp (tendsto_atTop_mono (show hikeV ≤ stackW from fun _=>Nat.le_add_right ..) goes_town))
 filter_upwards [h,hs.eventually_ge_atTop (4*pollN P+1:ℝ)] with d e t
 have he:(g d:ℝ)≤(φ d)^u:=by rw [coin_scale]; exact e
 let a:=φ d
 have hv:(4:ℝ)*(pollN P)+1 ≤a:=t
 have h0:0<(g d:ℝ):=by unfold girder trailerH; exact_mod_cast (show 0<g d by unfold girder trailerH; omega) -- tune
 have hi:1≤a:= Gleam.Luster.Risa.summitT _
 have hx:((4:ℝ)*(pollN P)+1)*(g d:ℝ) ≤a^(u+1):=by rw [pow_succ']; exact mul_le_mul hv he h0.le (zero_le_one.trans hi)
 have hZ: (4*pollN P+1)*g d ≤ intervalZ (stackW d) (u+1) P:= by exact_mod_cast (hx.trans (Nat.le_ceil _)|>.trans (le_refl _)) -- pow to interval
 exact ⟨he.trans (pow_le_pow_right₀ hi (Nat.le_succ _)),fun w p=>⟨raiseB (crews P w p 3|>.1) hZ,raiseB (crews P w p 3|>.2) hZ⟩⟩
where raiseB {o:Bool→ Cover}{a b:ℕ}(p:withinT o a)(q:a ≤ b):withinT o b:=fun i j=>by have h:=p i j; omega
#print axioms span_price
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
