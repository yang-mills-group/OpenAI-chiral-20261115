import ZecaPelican
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
open Regis.Circuit -- Aster





open _root_.YM.ZecaSky


variable (F:P.Nib 3 (P.advocate 3 x 3))(sc:ℕ→ℂ)(seq:ℕ→ℕ)
def Pentadose(d:Vantage):Prop:=∃k:ℕ,∃v:Cover,∀a,d a=(v a:ℝ)/5^k

lemma echolocation(p:Plume_LocalFieldBounds){d:Vantage}(b:Pentadose d)(t:ℕ)(l:ℤ):
 ∃y:Plume_LocalFieldBounds, y.pose=reecho p.pose d t l:=by
 obtain ⟨k,c,e⟩:=b
 let m:Cover:=fun a=>
    p.num a*5^k+(if a=3 then (t:ℤ)*5^(p.k+k) else c a*l*5^p.k)
 have h: 0 < m 3:=by
    simp only [m,ite_true]
    have :=p.u
    positivity
 refine ⟨⟨p.k+k,m,h⟩,?_⟩
 funext a
 change (m a:ℝ)/5^(p.k+k)=_
 unfold m reecho Plume_LocalFieldBounds.pose
 rw [e]
 split<;>push_cast<;>simp only [pow_add]<;>field_simp<;>ring

variable {P x F sc seq}
lemma reef (h:P.Mach x F sc seq) {p:Plume_LocalFieldBounds}
 (a:P.aboveRoof p){d:Vantage} (v:Pentadose d):
 P.Reef x F sc seq p.pose d:=by
 intro t i j
 obtain ⟨y,m⟩:=echolocation p v t i
 obtain ⟨z,n⟩:=echolocation p v t j
 simp_rw [← m,← n]
 have b:= le_trans a (le_add_of_nonneg_right (t.cast_nonneg (α:=ℝ)))
 exact h y z (by unfold aboveRoof Plume_LocalFieldBounds.tar; rw [m,echo3]; exact b)
             (by unfold aboveRoof Plume_LocalFieldBounds.tar; rw [n,echo3]; exact b)

/-- Actual G4, any Plume_LocalFieldBounds, UV scales. -/
theorem ibis (h:P.Mach x F sc seq) (b:P.Bottle 3 (P.advocate 3 x 3) F)
 {p:Plume_LocalFieldBounds} (a:P.aboveRoof p) {d:Vantage} (r:d 3=0) (t:d≠0)
 (v:Pentadose d) :
 P.RV x F sc seq p.pose d:=by
 unfold aboveRoof Plume_LocalFieldBounds.tar at a
 exact reef_rv _ _ _ _ _ _ _ b (by linarith only [a,P.roof.cast_nonneg (α:=ℝ)])
    r t (reef h a v)
#print RV
#print axioms ibis
