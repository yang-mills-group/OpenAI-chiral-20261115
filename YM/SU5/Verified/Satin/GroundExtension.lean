import YM.SU5.FiniteGaugeData.Tower.RimTone
/-! Attach the existing coherent tower to a specified universal Satin law, retaining E. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 380000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SatinVerification
open Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set
variable {Λ:Preparation}{lp:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus lp))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

structure GroundExtension where
  refine : ℕ → Family (tent Y H) → Family (tent Y H)
  rows : ℕ → ℕ
  columns : ℕ → ℕ
  history : Coherent (i := i) (k := k) (E := E) Y H refine rows columns
  clipped : Clipped Y H (i ∘ rows) (k ∘ columns)

include V in
theorem extend_ground : Nonempty (GroundExtension (i := i) (k := k) (E := E) Y H) := by
  obtain ⟨q, line⟩ := purchase_line Y H V
  obtain ⟨D, a, b, history, _, clipped⟩ := SlabMark.subs Y H V line
  exact ⟨⟨D, q ∘ a, b, history, clipped⟩⟩

theorem ground_projection (G : GroundExtension (i := i) (k := k) (E := E) Y H)
    (j : Axis) (strict : Bool) :
    ∃ C : Arena Y H G.history.circuit j 0 strict,
      floorV Y H G.history.circuit j 0 strict C ∈ Vacancy.Aurora Y H V G.history j strict C ∧
      ∀ x : Ark.Ht Y H G.history.circuit j 0 strict C,
        Tendsto (fun n => (Console.sky (office Y H V n G.history j strict C) (look j)) x)
          atTop (𝓝 ((Vacancy.Aurora Y H V G.history j strict C).starProjection x)) := by
  obtain ⟨C⟩ := voyage_H Y H V G.history.circuit j 0 strict
  exact ⟨C, Vacancy.belongs Y H V G.history j strict C,
    Vacancy.strands Y H V G.history j strict C⟩

end YM.CF.Buffered.Afterglow.Tower.SatinVerification
#print axioms YM.CF.Buffered.Afterglow.Tower.SatinVerification.ground_projection
