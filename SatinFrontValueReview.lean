import YM.SU5.Thin.Geometry
import SatinThinCollapse
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon

variable (Z : Lead.Clan) {P : Spine} {c r : ℕ → ℕ} {x : P.Spectrum0 3}
  {K : P.Register} {J : P.Ellis 3 x} (B : Experiment P K c r x J)
local notation "ξ" => P.advocate 3 x 3
local notation "Ψ" => P.seasons 3 ξ
local notation "H" => P.ManyF 3 ξ
local notation "R" => P.physicalEnergy 3 ξ
local notation "G" => P.ColorHil 3 ξ
local notation "E" => (Ψ).E
local notation "ρ" i:max => P.dew (c i) (r i)
local notation "ϕ" i:max => P.birthCloud x Z (c i) (r i)
local notation "λ'" => (P.enter 3 ξ)
local notation "z" => ((purePrice Z : ℝ) : ℂ)
local notation "ω" => P.colorZero 3 ξ
local notation "Ω" => P.heaven 3 ξ

include B
/-- The physical vectors for both uncentered front insertions have a joint limit
on one Satin election at a fixed positive time. The support statement refers
to the corresponding literal aprons at those same levels. -/
theorem reviewFrontPair (W : Lead.Clan) (T : P.Transmission x c r)
    (a : ℝ≥0) (ha : 0 < a) :
    (∀ ε > 0, ∀ᶠ i : ℕ in atTop, ∀ V : Lead.Clan,
      P.ThinIntrinsic (P.thinString V (c i) (r i)) ε ∧
      P.ThinIntrinsic ((P.thinString V (c i) (r i)).kiss P 3) ε) ∧
    Tendsto (fun i : ℕ =>
      inner ℂ ((R).E a (P.shard x Z (c i) (r i)))
              ((R).E a (P.shard x W (c i) (r i)))) atTop
      (𝓝 (inner ℂ (((purePrice Z : ℝ) : ℂ) • ω)
                   (((purePrice W : ℝ) : ℂ) • ω))) := by
  refine ⟨thin_widths T, ?_⟩
  have gap : Tendsto (fun i : ℕ => (a : ℝ) / P.dew (c i) (r i)) atTop atTop :=
    thin_compare_dew B ha (t := fun _ => a) (Eventually.of_forall fun _ => le_rfl)
  exact (thin_front_shard_tendsto Z B (fun _ => a) gap).inner
    (thin_front_shard_tendsto W B (fun _ => a) gap)

/-- At positive time the uncentered front pair has a nonzero rank-one
limit. This is the raw physical vector pairing, before identification with
the finite-grid readout of the two fixed smooth smears. -/
theorem reviewFrontPairValue (W : Lead.Clan) (T : P.Transmission x c r)
    (a : ℝ≥0) (ha : 0 < a) :
    (purePrice Z : ℂ) * (purePrice W : ℂ) ≠ 0 ∧
    Tendsto (fun i : ℕ =>
      inner ℂ ((R).E a (P.shard x Z (c i) (r i)))
              ((R).E a (P.shard x W (c i) (r i)))) atTop
      (𝓝 ((purePrice Z : ℂ) * (purePrice W : ℂ))) := by
  refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.mpr (purePrice_p Z).ne')
    (Complex.ofReal_ne_zero.mpr (purePrice_p W).ne'), ?_⟩
  simpa [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K,
    P.norms_color, mul_comm] using (reviewFrontPair Z B W T a ha).2

#print axioms reviewFrontPairValue
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
