import WakeRoad.Rogate
import WakeRoad.Tallow
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open ArborJet Preparation Yoke.ArborJet
open Dial Pressure Stationary Regis.Circuit
open CF.Onyx
open CF.Gingham.Ruff Spine.Gingham.VoyageB
open UVNext.FreeStress
variable (P:Spine)(r:ℕ→ℕ)
local notation "iₛ" i:max=>P.period (P.projection.rows (r i))
local notation "kₛ" i:max=>P.cutoff (P.projection.columns (r i))
local notation "nDoc" s:max i:max=>side P.run (iₛ i) s
local notation "Mₛ" s:max i:max=>P.par.V.L.H ((P.run).uv (kₛ i)-s)
local notation "R*" s:max=> ((↑(2*ArborJet.moment P s:ℕ):ℂ))
local notation "ff"=> (4* Maxwell.normal)
variable {m:ℕ}
variable (s n:ℕ)
local notation "K"=>RootBook P.run (iₛ n) (kₛ n) s
local notation "ι"=>Postcard ((K).p.B/10)
variable {a c μ:ℝ}{l:ℕ}{δ C:ℝ}(B:Scene P a c μ l s (P.period (P.projection.rows (r n))) (P.cutoff (P.projection.columns (r n))))(X:Rialto 6 P.par.d δ C)
local notation "A*" b:max=> grove P s (iₛ n) (kₛ n) b
local notation "w*"=> cocoa P s (iₛ n) (kₛ n) B X
local notation "G*" b:max=>combo P s (iₛ n) (kₛ n) B X b

open Regis.Wake
local notation "Ω"=>side P.run (iₛ n) s
local notation "τ"=>reachCost P.run s (iₛ n) (kₛ n)
def leaseR(c:Clip):ℝ:=Gleam.Wake.Vessel.cap c 2
lemma ceiling (R:ℝ)(b:Bool) (p: |reachCost P.run s (iₛ n) (kₛ n) R| ≤ 2): ‖atlas P r s n B X R b‖ ≤ (2*WakeRoad.coin (w*)) * assay 2 (leaseR P.par.K.top.clip) (Fintype.card ι):=by
 let c:=P.par.K.top.clip
 let k:=P.run.uv (kₛ n)-s
 let S:=stamen (P.par.V.L.mood k) (P.par.V.L.tied k) (More (Ω)); let V:= A* b; let D(j:ι):StrongDual ℝ (↥S):= (V.siphon ((τ) R) 1 0 c j).comp S.subtypeL
 let T:=G* b
 have hp(i:ι) : ‖D i‖≤leaseR c:= (V.siphons_clamp ((τ) R) _ _ _ _ _).trans (mul_le_mul_of_nonneg_right (p.trans_eq (by norm_num)) (by positivity))
 change ‖seatT P.run s (iₛ n) (kₛ n) V (WakeRoad.Score T) R‖ ≤ _
 exact le_trans (Paint.soak D (score_sol T) (leaseR c) hp|>.2) (Eq.le (by unfold T ArborJet.combo; rw [portrait_coin]))
