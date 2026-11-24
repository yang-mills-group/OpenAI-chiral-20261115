import YM.SU5.Selected.Actress.Shape
import YM.SU5.Selected.Actress.Purity
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
local notation "Σ₀"=> Actress.Label Y H j r
local notation "Pη"=> Label.money Y H V Q Qc j r C U
local notation "Z" x:max=> balcony J x
-- Chronometry. at resolution evaluate in chronological order (earliest on left). Points are *empty separation* in gaps, **in addition** to widths! n shifts>=0 times. spine recursively. Applicability $u: ∀ cal-i rank ≤ s$ (finite labels use subtype or Fin).
open YM.Boundary (Distn Probe)
variable {κ:Type*} [Fintype κ] [DecidableEq κ](F:κ→Label Y H j r) (L:List κ) (s:ℕ)
local notation "γ" L:max=> Quantity Y H V Q Qc j r C U F L
local notation "K₀" L:max=> onArc Y H V Q Qc j r C U F L
local notation "E₀"=> marked Y H V Q Qc j r C χ
local notation "Z₁" i:max z:max v:max=> lode Y H Q j r i F v z L -- parens ℝ
local notation "T₀" s:max=> whenly (timeMesh Λ) s
local notation "π" s:max z:max=> Spectral.Alps.imaginary (fun i:κ=> (T₀ s) (z i)) -- name collision Real.pi; specify PIB
include V Q Qc C U
structure Scores (L':List κ) : Prop where -- redefinition L to avoid shadow macro
 age: Continuous (γ L') ∧ AnalyticOnNhd ℂ (γ L') (waist κ)
 hiked (s:ℕ)(p:∀ i,(F i).count ≤ s)(z:κ→ℕ) : let x:= lode Y H Q j r s F p z L'; (γ L') (Spectral.Alps.imaginary (fun t:κ=>whenly (timeMesh Λ) s (z t)))= E₀ s (toTest Y H j r s x) ∧ CovCover K x.val
 decides (i:ℕ)(f:(κ→ℂ)→ℂ) (hf:ContinuousOn f (ivory κ))(p:AnalyticOnNhd ℂ f (waist κ)) (z:∀ (s:ℕ), i ≤ s→∀ p:∀ i,(F i).count ≤ s,∀ z:κ→ℕ, f (π s z)=E₀ s (toTest Y H j r s (lode Y H Q j r s F p z L'))) : Set.EqOn f (γ L') (ivory κ)
 pays (t:ℝ)(x:κ→ℝ): (γ L') (fun i=>(x i:ℂ))= inner ℂ λ₀ ((Spectral.Alps.arms (J) (fun i=> Pη (F i)) t L' x) λ₀)
 novel (x: Probe (κ→ℝ)):stackPrice Y H V Q Qc j r C U F L' x=(∫ i,x i*(γ L') (fun j=>(i j:ℂ))) -- binder j **shadow** γ inside lambda perimeter? gamma BEFORE j; fix.
 foresight (x: Probe ℝ)(u:κ→ℂ)(a b:List κ)(i:κ) (hi:i∉a)(hk:i∉b)(k: L'=a++i::b)(p:HasCompactSupport ⇑x)(e:tsupport x ⊆ Set.Iio 0): (∫ p:ℝ, (γ L') (Function.update u i (p:ℂ)) * Boundary.Probe.hat x p)=0
#print Scores.mk
lemma attends : Scores Y H V Q Qc j r C U F L := ⟨quota ..,fun s p i=> ⟨amountQuota .., picks Y H V Q Qc j r C U s F p i L⟩,decisive Y H V Q Qc j r C U F L, Actress.window Y H V Q Qc j r C U F L, collection Y H V Q Qc j r C U F L, forecast Y H V Q Qc j r C U F L⟩
structure Chronicle : Prop where
 stays: Borough Y H V Q Qc j r C U
 staunch: (Spectral.Alps.evolve J).Spectrum (Alps.spectralP J)
 esteem: (Alps.spectralP J).region (Set.Iio 0)=0
 fact (v:ℕ)(L:List (Fin v))(f:Fin v→Label Y H j r): Scores Y H V Q Qc j r C U f L
 gauge: DenseRange (fun F: Label Y H j r=> Pη F λ₀)
#print Chronicle.mk
lemma played (v:LoneVac Y H V Q Qc j r C U): Chronicle Y H V Q Qc j r C U:= ⟨resolves Y H V Q Qc j r C U v, Alps.moment _,Alps.bright_region _,fun i l f=>attends .., podium Y H V Q Qc j r C U⟩
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms Chronicle
#print axioms Scores
#print axioms played
#print axioms attends
