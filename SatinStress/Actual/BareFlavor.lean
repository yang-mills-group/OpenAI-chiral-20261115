import YM.SU5.Six.Elected
import SatinStress.Actual.WilsonGeneration

/-! Exact bare flavor invariance on the shared Satin preparation. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 800000
set_option maxRecDepth 6000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open SatinStressData (Flavor)
variable (P : Spine) (i k : ℕ)
local notation "level0" => P.run.uv k
local notation "τ" => (P.run.meter.a level0).threshold
local notation "N" => side P.run i level0
local notation "Ξ" => ((P.run.voyage i).X level0).gram level0
local notation "ℓ" => (P.run.voyage i).CapeT level0
local notation "U_" v => changeM (m:=Vale.mesh (P.run.ir i) P.par.R.L (P.run.uv k)) P.par.U v babyM
local notation "Γ(" g ")" => SatinStressData.gen N (SatinStressData.turn g)

theorem intrinsic_sea (z : Orbit N) (g : Flavor) (he : flags τ z.1 = ∅) :
    acts (quant Γ(g)) (U_ z.1)=U_ z.1 := by
  obtain ⟨safe, p, life, _⟩ := P.bare_chiral i k _ he
  rw [p] at life
  exact SatinStressData.flavor_here (Cube.links z.1) _ _ safe life g

theorem inherited (z : Orbit N) (g : Flavor) : acts (quant Γ(g))
    (denZ Ξ P.par.U ℓ z) = denZ Ξ P.par.U ℓ z := by
  rw [P.bare_density]; unfold Vale.capP; by_cases he : flags τ z.1 = ∅
  · rw [Set.indicator_of_mem (show _ ∈ {U | flags τ U = ∅} from he),map_smul,
        intrinsic_sea P i k z g he]
  rw [Set.indicator_of_notMem (show _ ∉ {U | flags τ U = ∅} from he),map_zero]

#print axioms intrinsic_sea
#print axioms inherited
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
