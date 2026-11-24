import WakeRoad.Patera
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
abbrev atlas (R:ℝ)(b:Bool):ℂ:=seatT P.run s (iₛ n) (kₛ n) (A* b) (WakeRoad.Score (G* b)) R
abbrev visage (R:ℝ):ℂ:= seatT P.run s (iₛ n) (kₛ n) (planter (fun b=> (A* (!b)))) (brushpot (fun b=> (G* (!b)))) R

lemma scaledAtlas (τ:ℝ)(_t:s ≤ P.run.uv (kₛ n)):
 let ν:=reachCost P.run s (iₛ n) (kₛ n) τ
 let W:=cocoa P s (iₛ n) (kₛ n) B X
 (R* s)^8 * (visage P r s n B X τ - atlas P r s n B X τ true * atlas P r s n B X τ false)=(ν:ℂ)^4 * affinity (salute P r s n) (portrait true W) (portrait false W) :=by
 intro ν W
 let k:=P.run.uv (kₛ n) - s
 have z:=P.par.V.L.roof k; let T (b:Bool):= (A* (!b)); let R(b:Bool):= (G* (!b))
 have he:=regally (P.par.V.L.mood k) (P.par.V.L.tied k) P.par.K.width R T ν (z.2.1 _) z.1 -- arg order
 have t : visage P r s n B X τ-atlas P r s n B X τ true * atlas P r s n B X τ false =(ν:ℂ)^4 * affinity (chipbook (M:=Mₛ s n) (T true) (T false)) (R false) (R true) := he
 change (↑(2*ArborJet.moment P s:ℕ):ℂ)^8 * (visage P r s n B X τ-_) = _; rw [t]
 unfold affinity salute; simp_rw [mul_sum]
 refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=>sum_congr rfl (fun t _=>sum_congr rfl (fun d _=>?_))))
 unfold R T W ArborJet.combo; dsimp only [Bool.not]; ring -- R combo false and portrait. leftover
