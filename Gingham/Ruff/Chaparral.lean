import Gingham.Ruff.Masque
import Gingham.Ruff.Terrace
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s



def Anthem (ρ t:ℝ) (X:Rialto 6 P.par.d ρ t) :=
   ∀ᶠ s in atTop,
    ∀ i k,∀ h:Scene P a c μ d s i k,
      Arioso X h.gb.pump h.bre ∧
       ∀(z:Shape)(U:UNI SpinIdx), Arioso X (framed z U h.gb.pump) h.bre

theorem singalong (ha:0<a):
  ∃ ρ t X, 0<ρ∧ Anthem P a c μ d ρ t X:=by
  obtain ⟨ρ,t,u,x⟩:=libretto 6 _ P.par.dpos
  refine ⟨ρ,t,x,u,?_⟩
  filter_upwards [ (turnover P.par).eventually (wharf_fee _ _ ha u)] with s v i k h
  have f:= v _ h.gears.boot
  have y:= well_pitch _ h.room
  have l:(~p~ s)=(R s i k).p:=
       (((P.run.voyage i).X (P.run.uv k)).pull.owns s h.ok.le).width


  rw [l] at y
  exact ⟨ recitativo x _ h.gears.tag f _ y (pitched_plain x h.gears.worn.1 _),
     fun z U => recitativo x _ h.gears.tag f _ y (pitched x h.gears.worn.1 _ z U)⟩

lemma Cosmos.anthem (v:Cosmos P a c μ d):∃ ρ t X,
     0<ρ∧ Anthem P a c μ d ρ t X:=singalong P a c μ d v.aP

#check @Cosmos.anthem
#print axioms Cosmos.anthem

