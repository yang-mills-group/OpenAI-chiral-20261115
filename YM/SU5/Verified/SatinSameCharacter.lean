import YM.SU5.Selected.Interpret
import YM.SU5.Selected.Sustain
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
namespace SameCharacter
open Theory
/-- The two worker interfaces use the identical closed algebra of compressed
observables on the ground space of a specified Satin history and axis. -/
theorem sameAlgebra :
    catalog Y H V G j strict C = Selected.displayAlgebra Y H V G.history G.clipped j strict C := rfl

/-- Realize any given panel character as a resident without making a new
spectral selection. -/
noncomputable def resident
    (c : Selected.displayAlgebra Y H V G.history G.clipped j strict C →⋆ₐ[ℂ] ℂ) :
    Resident (catalog Y H V G j strict C) :=
  WeakDual.CharacterSpace.equivAlgHom.symm c.toAlgHom

theorem eye_resident
    (c : Selected.displayAlgebra Y H V G.history G.clipped j strict C →⋆ₐ[ℂ] ℂ)
    (a : catalog Y H V G j strict C) :
    eye (resident Y H V G j strict C c) a = c a := rfl

/-- The selected evaluations agree on every common local observable and level,
with the same character, including a character elected by Glasshouse. -/
theorem sameReading
    (c : Selected.displayAlgebra Y H V G.history G.clipped j strict C →⋆ₐ[ℂ] ℂ)
    (s:ℕ) (f:observable (tent Y H) strict) :
    markE Y H V G strict j C (resident Y H V G j strict C c) s f =
      Selected.response Y H V s G.history G.clipped j strict C c f := rfl

/-- Transfer the surviving matrix element to the other presentation of the
same character at its actual observation level. -/
theorem readingFloor
    (c : Selected.displayAlgebra Y H V G.history G.clipped j strict C →⋆ₐ[ℂ] ℂ)
    (s:ℕ) (f:observable (tent Y H) strict) (u:ℝ)
    (h : u ≤ ‖Selected.response Y H V s G.history G.clipped j strict C c f‖) :
    u ≤ ‖markE Y H V G strict j C (resident Y H V G j strict C c) s f‖ := by
  rw [sameReading]; exact h
end SameCharacter
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
