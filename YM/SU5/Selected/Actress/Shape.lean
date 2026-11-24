import YM.SU5.Selected.Actress.Altar
import YM.SU5.Selected.Actress.Lemo
import YM.SU5.Selected.Actress.Cyclic
import YM.SU5.Selected.Choice
import YM.SU5.Selected.Actress.Area
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
variable (F:Label Y H j r)
include V Q Qc C U
-- Upgrade Mink time/Eu-width component with exact Ω. State normalized as in Algebra.L.<...>. haven't got x-motion continuous beyond mesh.
-- Qualifying directions: all Trans mesh c shifts (even criterion sufficient), r not matter strict. Real Mink TIME, not ℂ.
abbrev Acts (j:Axis):= ℕ × Trans j × ℤ
noncomputable def engage : Acts j → unitary U.H.Op:= fun x=> spatialU Y H V Q Qc j r C U x.1 x.2.1 x.2.2
local notation "Γ"=> engage Y H V Q Qc j r C U
lemma compVac (t:Acts j): (Γ t).val λ₀=λ₀:= travel_floor Y H V Q Qc j r C U t.1 t.2.1 t.2.2
lemma staysLine(x:U.H)(p:∀ i: ℝ ⊕ Acts j,(Alps.tickets (J) (Γ) i).val x=x) : x∈bottom Y H V Q Qc j r C U:= (Diary.staves Y H V Q Qc j r C U _).2 ⟨fun u=> p (.inl u),fun a b i=> p (.inr (a,b,2*i))⟩
lemma moves_ : Alps.JMotion (J) κ₀ Γ:= fun i=> ⟨fun t=> Diary.intimate Y H V Q Qc j r C U i.1 t i.2.2 i.2.1,fun F=> movesF Y H V Q Qc j r C U F i.1 i.2.1 i.2.2 (max i.1 F.count) (le_max_left ..) (le_max_right ..)⟩
abbrev Borough:=Alps.Urbana J λ₀ κ₀ Γ
local notation "ϱ"=> Borough Y H V Q Qc j r C U
lemma resolves (p: LoneVac Y H V Q Qc j r C U): ϱ:=by
 refine city J λ₀ _ Γ (vacuum_norm Y H V Q Qc j r C U) (fix_ground Y H V Q Qc j r C U) (podium Y H V Q Qc j r C U) (moves_ Y H V Q Qc j r C U) (compVac Y H V Q Qc j r C U) (fun i t=> Submodule.mem_span_singleton.mp ?_)
 exact (p ▸ (staysLine Y H V Q Qc j r C U _ t))
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms engage
#print axioms resolves
#print axioms moves_
