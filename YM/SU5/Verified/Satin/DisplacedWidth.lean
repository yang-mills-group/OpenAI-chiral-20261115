import YM.SU5.Selected.Prag.Burn
import YM.SU5.Selected.Prag.Risk
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (C : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
namespace Summer
open Germ
open Tapestry CF.Pannier.Chancel.Attic.Cairn
open Spectral Spectral.Alps Germ.Alliance
open Fern Fern.Curtain Fern.Planet
open CF.Pannier.Chancel.Attic.Cairn.Giant CF.Pannier.Chancel.Attic.Cairn.Giant.Voice
namespace Mills
variable (s:ℕ)(j:Axis)(X:Giant){W:Window.Family} (F G:X.SpireBook (tent Y H) W) -- fix
local notation "R"=> X.Broad
variable (χ:CapCharacter Y H V Q Qc 3 false (C 3))
local notation "Θ"=> escort Y H V Q Qc 3 false (C 3)
local notation "B₁" v:max=> (Θ v (C v) χ)
variable (U: Birthplace Y H V Q Qc 3 false (C 3) (escort Y H V Q Qc 3 false (C 3) 3 (C 3) χ))
variable (x₀: Voice.Tonic X) {c:ℝ}(p: Planet.Saturn Y H V Q Qc C s X F G χ x₀ c)
local notation "ℓ"=> declination' Y H X
local notation "L"=> (3:Axis)
local notation "y₀"=> (Voice.ink X K F x₀).val
local notation "y₁"=> (Voice.burnish X K F G x₀).val
local notation "y₂"=> (Voice.flame X K F x₀).val
local notation "V₀"=> Summer.Polaris Y H V Q Qc L false (C L) U
local notation "Γ₀"=> Summer.terse Y H V Q Qc C L χ U
local notation "S"=> Summer.skyline Y H V Q Qc C L χ U
local notation "Σ"=> Diary.jetTime Y H V Q Qc L false (C L) U
local notation "κ"=> markedActor Y H V Q Qc L false (C L) U s
local notation "K₁" x:max=> Γ₀ (κ x)
local notation "Δ"=> whenly (timeMesh Λ) s 1
local notation "Ω"=> terse Y H V Q Qc C L χ U (vacuum Y H V Q Qc L false (C L) U)
local notation "Ξ"=> Actress.Label Y H L false
local notation "Φ"=> (V₀).Realm (look L)
local notation "F₊"=> (Tower.Field Y H s L 0 false)
local notation "ρ"=> Torrent.fare
local notation "τ"=> relocate (tent Y H) L
local notation "W'"=> Summer.worldShelf Y H V Q Qc C L χ U
-- prove both strict evolution & cast. actual Burn, not theoretical before anywhere.
local notation "ν" y:max z:max f:max=> Library Y H V Q Qc C L s χ U y z (declination' Y H X) y₀ f X.ascY X.ascX
variable (x y z:Tower.Field Y H s 3 0 false)(tX: Library Y H V Q Qc C 3 s χ U x y (declination' Y H X) (Voice.ink X (tent Y H) F x₀).val (Voice.burnish X (tent Y H) F G x₀).val X.ascY X.ascX) -- goal term syntax notation variable? x uses F₊ bug! use explicit
    (tZ: Library Y H V Q Qc C 3 s χ U x z (declination' Y H X) (Voice.ink X (tent Y H) F x₀).val (Voice.flame X (tent Y H) F x₀).val X.ascY X.ascX)
/-- On the same selected skyline, translating a positive-width identity slab
to any space and time still leaves it noncommuting with the calibrated operator. -/
theorem Fierce.displaced_width_noncommutes {D0 D1 : Actress.Label Y H 3 false}
    (f : Fierce Y H V Q Qc C s X F G χ U x₀ x y z D0 D1)
    (height ticks : ℕ) (ht : 0 < ticks) (timeShift : ℝ) (spatial : OS.Cross 3) :
    ¬ Commute (Alps.conduct S timeShift
      (W' (slabC Y H 3 height ticks ht, spatial))) (W' (D0, 0)) := by
  rw [timeless Y H V Q Qc C 3 height χ U ticks ht timeShift spatial]
  exact f.crossedD _ (MeshClock.when_pos (timeMesh Λ) height ticks ht)

end Mills
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
