import ZecaTeam
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ






open SatinJets SatinNucleus Six Germ Alliance

variable
 (Y:ℕ→P.Apron) {V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
 (F:P.Nib 3 (P.advocate 3 x 3))

lemma ruby_O (A:P.Apron)(a b:ℝ):
 P.ruby 3 ξ A 0 a b ω=π (P.beamRaw 3 x A a):=by
 let w:=A.realWidth P 3
 rw [P.ruby_price, P.dazzle_zero,← P.beam_bank] -- beam_bank opposite
 change (Η).E (a-w).toNNReal (P.coffer 3 ξ (A.engine P 3 ξ) ((Η).E (b-w).toNNReal ω))=_
 rw [P.heaven_hot]
 rfl

lemma across_mead
 (l:GalaxyShow P x f k Y V)
 (q:NibLine P 3 (P.advocate 3 x 3) F Y 1)
 {a b:ℝ}(p:0<a)(t:0<b):
 F a b ω = π (V 3 [] a):=by
 have h:=(π).continuous.continuousAt.tendsto.comp (l.heat.cash 3 [] a p)
 apply tendsto_nhds_unique ((q.dyeOne p t).seeks ω)
 exact h.congr (fun i=> (P.ruby_O x (Y i) a b).symm)
#check LinearIndependent.ne_zero
#print Seven

def MyJet:Prop:=∀ a b:ℝ, 0<a → 0<b → F a b ω ≠ 0
lemma shoot_again
 (l:GalaxyShow P x f k Y V)
 (q:NibLine P 3 (P.advocate 3 x 3) F Y 1):
 P.MyJet x F:=by
 intro a b j h p
 have t: P.wealth 3 ξ (V 3 [] a)=0:= (P.across_mead x Y F l q j h).symm.trans p
 exact (l.independence a j).ne_zero 0
      ((congrArg (P.epochW x f k 0) t).trans (map_zero _))
#print axioms shoot_again
