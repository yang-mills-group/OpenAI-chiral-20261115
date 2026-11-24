import YM.SU5.Selected.Actress.Basket
import YM.SU5.Selected.Actress.Scarves
import YM.SU5.Selected.Actress.Moves
import YM.SU5.Selected.Euro.Palate
import YM.SU5.Selected.Time.Prom
/-! Observables CP6. Select & reconstruct continuous **physical time**, no spectator semantics. Includes concurrence test of spatial mesh motions. Test spacings as Vanguard. ( `monoAxis U` has dummy spatial even though real mesh is present; `stay` keeps only relevant time facts expressed with spectralP pushed to ℝ of THAT operator system). -/
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
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Β" => pruner Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "U₀" s:max => timePruner Y H V Q Qc j r C s
local notation "p₀" s:max => spacePruner Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "P₀" s:max => stretches Y H V Q Qc j r C s
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "η₀" => leave Y H V Q Qc j r C U
open Companies
namespace Actress
open Tapestry
open Spectral Spectral.Alps
local notation "J"=> Diary.jetTime Y H V Q Qc j r C U
local notation "Σ₀" => Label Y H j r
local notation "κ₀"=> Label.money Y H V Q Qc j r C U
local notation "Vγ"=> incubate Y H V Q Qc j r C U
local notation "ψ"=> travel_χ Y H V Q Qc j r C U
-- time-only observer candidate. NOT a Mink local-observable net, just the real-time/dense-space *-algebra of pre-localized **time-slab bounded** operators with time-width attributes (those aren't support bounds after Mink evolution). Define time-transport group on it. Euclidean test supports still spatial/t labels. Spatial covariance only mesh & height-specific signals; actor algebra preserved as well. Amenable discreted spacetime subgroup.

variable (F:Label Y H j r)
include V Q Qc C U
lemma fix_ground : λ₀∈ (J).ground:= (OS.Semigroup.fixed ..).2 (time_floor Y H V Q Qc j r C U) -- ambiguity defeq
-- star Label. orientation to strict truth. `mirror = theta at gaugeT`. keep width & prefect. 
noncomputable def Label.rev : Label Y H j r:=by
 let f:=inverse Y H F.count j r F.span F.appraise
 have he: CovCover K f.val.val:=covariant_flips K j (gaugeT K F.span) (test_entry Y H F.count j r F.appraise).paid.choose_spec F.ward
 exact ⟨F.count,F.span,F.paid,f,he⟩
lemma Label.rest : κ₀ (F.rev Y H j r)=star (κ₀ F):= (reverses Y H V Q Qc j r C U F.count F.span F.appraise F.paid).symm
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress

#print axioms Label.rest
#print axioms fix_ground
