import YM.SU5.Assay.Pan
import YM.SU5.Assay.CharterCost
import YM.SU5.Six.PressSmear
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Result of holding a raw pose inscription in one chart (alignment
 at absolute address 0), and projecting and sampling continuously.
-/
local notation "φ"=>P.locate j x
local notation "π"=>P.reprise j x
def stirring (u:Vantage→X):Vantage→Y:= fun y=>φ y (π (u y))
local notation "M"=> P.stirring j x
def stirred (F:SampleDose)(u:Vantage→X):Y:= mixedCup volume F.val (M u)
local notation "κ"=>P.stirred j x
variable {F:SampleDose}{C:ℝ}{u:Vantage→(P.ColorHil j x).Op}
lemma stirring_cont (p:AtPan F.val u):AtPan F.val (M u):=by
 intro y t; exact P.locate_limit j x tendsto_id (P.reprise_bsot j x (p y t))
lemma stirring_cost (p:PanC F.val u C):PanC F.val (M u) C:=
 fun y t=> (P.locate_credit ..).trans ((P.reprise_pay ..).trans (p y t))
lemma stirring_ink (p:AtPan F.val u)(w: PanC F.val u C):SInk volume (Pan F.val (M u)):=
 AtPan.booth F.smooth.continuous F.budget (P.stirring_cont j x p) (P.stirring_cost j x w)
lemma stirring_dagger (u:Vantage→X)(y:Vantage):star (M u y)=M (fun y=>star (u y)) y:=by simp only [stirring,P.locate_star,P.reprise_star]
lemma stirring_turn (p:AtPan F.val u):AtPan F.val (fun y=>star (u y)):=fun y t=> (p y t).dagger -- P j x explicit?
lemma stirring_turnC (p:PanC F.val u C):PanC F.val (fun y=>star (u y)) C:=fun y t=> (norm_star _).trans_le (p y t)
lemma stirred_read (p:AtPan F.val u)(w: PanC F.val u C)(b:B):
 κ F u b=∫y,(F.val y:ℂ) • (M u y b):=(P.stirring_ink j x p w).click _
lemma stirred_read_int (p:AtPan F.val u)(w: PanC F.val u C)(b:B):
 Integrable (fun y=>(F.val y:ℂ) • (M u y b)) volume:=(P.stirring_ink j x p w).body b
lemma stirred_turn (p:AtPan F.val u)(w: PanC F.val u C):star (κ F u)=κ F (fun y=>star (u y)):=by
 ext1 b
 refine (PanC.cupTurn F.smooth.continuous F.budget (P.stirring_cont j x p) (P.stirring_cost j x w) b (μ:=volume)).trans ?_
 simp_rw [P.stirring_dagger,P.stirred_read j x (P.stirring_turn j x p) (P.stirring_turnC j x w)]

-- earlier `φ -p` price restoration works likewise on integrals.
lemma located_cup {M₁ M₂:Vantage→Y}(y:Vantage)(t:∀p∈tsupport F.val,M₂ p= φ y (M₁ p))
   (u:SInk volume (Pan F.val M₁))(v:SInk volume (Pan F.val M₂)):
 φ y (mixedCup volume F.val M₁)=mixedCup volume F.val M₂:=by
 ext1 i
 change W y (SInt volume _ (W (-y) i))= SInt volume (Pan _ M₂) i
 rw [v.click,u.click, ←(W _).integral_comp_comm (u.body _)]
 refine integral_congr_ae (Eventually.of_forall fun q=>?_) -- binder shadows q here only
 dsimp only
 by_cases h:q∈tsupport F.val
 · unfold Pan; rw [t q h]; change W y ((F.val q:ℂ) • M₁ q (W (-y) i))=(F.val q:ℂ)•_;rw [map_smul];rfl
 have z:= image_eq_zero_of_notMem_tsupport h
 rw [pan_dry _ z,pan_dry _ z];change W y 0=0;exact (W y).map_zero
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
