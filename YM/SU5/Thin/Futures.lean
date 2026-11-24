import SatinFixedContrastNovember4
import YM.SU5.Thin.Deposit
import YM.SU5.Thin.Relative

set_option autoImplicit false
set_option maxHeartbeats 190000
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
open Sifter DoseBill VoucherOp PadThin Theatre
section positivity
variable {P:Spine}{K:P.Register}{x:P.Spectrum0 3}{J:P.Ellis 3 x}{r:ℕ→ℕ}
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ManyF 3 ξ
local notation "η"=> P.heaven 3 ξ
abbrev stopEarly : ℝ := -3
abbrev stopLate : ℝ:=3
abbrev latch : ℝ≥0 := 1/2
abbrev downDue : ℝ := 1/16
lemma down_pos : 0 < downDue:=by norm_num [downDue]
lemma latch_pos : 0 < latch:=by norm_num [latch]
variable (V:P.Repeater K x J r)
include V
lemma charterWeather : ∀ᶠ i:ℕ in atTop, ∀ (b:ℕ→ℕ), StrictMono b→(∀ j:ℕ,P.StaticPrice x i (r i) (b j))→ Weather P x latch downDue (r i) b:= by
  filter_upwards [V.horizonStays latch latch_pos downDue down_pos] with i u b t H' Z
  exact (t.tendsto_atTop.eventually u).mono fun i w k v=>(w (H' i) Z k v).le
omit V
private lemma doclock (x t:ℝ)(v:1≤t-x) : latch ≤ (t-x).toNNReal:= by
 apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal _ (by linarith : 0 ≤ t-x)]
 exact le_trans (by norm_num [latch] : (latch:ℝ)≤1) v
namespace VoucherOp
variable {n:ℕ}{b:ℕ→ℕ}{Z W:Lead.Clan} (U:P.VoucherOp x Z n b)(V:P.VoucherOp x W n b)
local notation "κ" => (↑(purePrice Z):ℂ)
variable {F G:SampleDose}
variable (h:Weather P x latch downDue n b)
include h
lemma afterTrue (f:G.Normalized) (g:tsupport G.val⊆ reviewLaterBox.invites) :
    dist (U.thinOp true G 0 stopLate η) (κ • η) ≤ purePrice Z/16:=by
  rw [show purePrice Z/16= downDue*purePrice Z from (by unfold downDue; ring)]
  apply trueDistance H G _ (fun p=> U.reachedPillar true p 0 stopLate) _ _ η (κ • η) (downDue*purePrice Z) (mul_pos down_pos (purePrice_p Z)).le _ f
  · intro i y; have he: latch ≤ (i 3-0).toNNReal:= doclock 0 (i 3) (by have ht : 1< i 3:= (g y 3 (Set.mem_univ _)).1; linarith)
    exact (congrArg (fun z:(H).Op=>dist (z η) (κ • η)) (U.reached_unad true i 0 stopLate)).trans_le (U.alongTrue latch downDue h i he)
lemma beforeTrue (f:F.Normalized) (g:tsupport F.val⊆ reviewEarlierBox.invites) :
    dist ((U.thinOp false F stopEarly 0).adjoint η) (κ • η) ≤ purePrice Z/16 := by
  rw [show purePrice Z/16= downDue*purePrice Z from (by unfold downDue; ring)]
  apply oppDistance H F _ (fun p=> U.reachedPillar false p stopEarly 0) _ _ _ _ _ (mul_pos down_pos (purePrice_p Z)).le (U.adjCont stopEarly 0 η) _ f
  intro i y; have he: latch ≤ (0-i 3).toNNReal:= doclock (i 3) 0 (by have ht : i 3 < -1:= (g y 3 (Set.mem_univ _)).2; linarith)
  exact (congrArg (fun z:(H).Op=>dist (z η) (κ • η)) (U.adjBackward i stopEarly 0)).trans_le (U.alongTrue latch downDue h i he)
lemma receives (v:F.Normalized)(u:G.Normalized)(f:tsupport F.val⊆ reviewEarlierBox.invites)(g:tsupport G.val⊆ reviewLaterBox.invites):
    let R:= inner ℂ η (U.thinOp false F stopEarly 0 (V.thinOp true G 0 stopLate η));
    ‖R-(purePrice Z:ℂ)*(purePrice W:ℂ)‖<purePrice Z*purePrice W/2 ∧ purePrice Z *purePrice W/2 < ‖R‖ :=
  pairStakes H (U.thinOp false F stopEarly 0) _ _ (P.stone_norm ..) (purePrice Z) (purePrice W) (purePrice_p Z) (purePrice_p W)
    (U.beforeTrue h v f) (V.afterTrue h u g)
end VoucherOp
end positivity
#print axioms VoucherOp.receives
#print axioms charterWeather
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
