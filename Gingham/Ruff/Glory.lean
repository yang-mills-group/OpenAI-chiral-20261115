import Gingham.Ruff.Sash
import SatinThinFusionPaleness
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



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false

open Six
variable {r : List (Axis×ℤ)} {f:Family P.calibration}

private lemma leaf_shine{n m:Side}(U:Mark n)(p:n=m)
    (a:∀x,U x∈ fockOne n)
    (g:∀x, ‖U x‖≤q):Shines ρ (Tapestry.arrange _ _ p U) q:=by
  subst m
  intro x
  change Bright ρ (U x) q
  obtain ⟨z,u⟩:=Submodule.mem_span_singleton.mp (a x)
  specialize g x
  rw [←u] at g ⊢
  
  exact ((Bright.mint (I:=Single n)).scale z).raise
    (by simpa only [norm_smul,norm_one] using g)

lemma shining_paleness (a:Paleness P.calibration f)(b:pay f q):
   Shining P ρ s i f q:=by
 intro r
 have x: Paleness K (Ballet r f) ∧ pay (Ballet r f) q:=by
    induction r with
    | nil=> exact ⟨a,b⟩
    | cons x r ih=>exact ⟨mirror_pale _ _ ih.1 _ _,pay_flips K ih.2 _ _⟩
 exact leaf_shine _ _ (x.1 (momentm Y i s)) (x.2 _)

#print axioms shining_paleness
#check pale_iff


/-- qualified gauge-price, landing gauge. includes True pay receipt from Rosie. -/
lemma GaugePrice
   {S:Finset Cover}{A:Cluster P.calibration}
   {ν:ℕ→ℕ}
   (b:Bouquet S v true A)
   (p:∀ᶠ n:ℕ in atTop,pay (A (some n)) q):
   Regalia P ρ s ν S A q ∧ PureGauge P.calibration (inLeaf b.check.landing):= by
 have z(i):Paleness P.calibration (A i):=by
    intro m x;obtain ⟨u,l⟩:=(b.pays i).2.2.2 rfl m x
    rw [l]; exact Submodule.mem_span_singleton.mpr ⟨u,rfl⟩
 have u:0≤q:=by obtain ⟨n,h⟩:=p.exists;exact pay_nonneg (F:=A (some n)) h
 exact ⟨⟨b.check,(enclave_spec _).mpr (b.pays none).2.1,u,
   p.mono (fun n t=>shining_paleness (z (some n)) t)⟩,
   (pale_iff P _).mp (z none)⟩
#print axioms GaugePrice

