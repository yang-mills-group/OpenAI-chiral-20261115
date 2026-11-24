import VerifiedSatinNovember4Updates
import YM.SU5.Macro.Transverse
import YM.SU5.Macro.Travel

/-! # First endpoint — the obstruction at positive energy, no need for identity Label

Compare `Fierce.displaced_width_noncommutes`. Even if **throwing away that
identity Label**, it already fails for the interaction pair themselves, and indeed
for any operators retaining their very vacuum vectors in Skyline. Everything on the same
character and phase histories of checkpoint 9's `docket` (`OnOrion`, `Season.Equilis`).
`Fierce.ticket` is an analytic (and positive) bill: along *each* real forward spatial
axis, nonzero passage with a finite analytic allowance. See `Ticket.journeys`
for how to query even if wishing to retain merely the separated heat-kernel readings on
some fixed recognition scheme for those macroscopic fields, instead of both precise operator
labels. Will develop also the identification and smearings.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 440000
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
variable (s:ℕ)(j:Axis)(X:Giant){W:Window.Family} (F G:X.SpireBook (tent Y H) W)
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

open Relief Bornology
local notation "Θ'" u:max t:max => _root_.YM.SatinMacro.joinST u t
local notation "e·" k:max => Relief.aim 3 k
local notation "σ" => (Summer.skyline Y H V Q Qc C 3 χ U).unit
local notation "read" x:max y:max => _root_.YM.SatinMacro.kernel (S) (K₁ x) (K₁ y)
variable (p' : Trans 3)
lemma skyline_static (v:E4) : (σ).translation v Ω = Ω :=
  _root_.YM.SatinMacro.static (S) Ω (Summer.wHeat Y H V Q Qc C L χ U)
    (Alliance.follows_full (V₀) (daylight (timeMesh Λ)) (Σ) (source_heat Y H V Q Qc L false (C L) U)
      (vacuum Y H V Q Qc L false (C L) U) (Summer.owns_vista Y H V Q Qc C L χ U)) v

variable {f g: Family (tent Y H)} {M N:Finset Cover} {w: Axis→ℤ}
include V Q Qc C U
lemma Library.ticket (x y:Tower.Field Y H s 3 0 false)
    (h : Library Y H V Q Qc C 3 s χ U x y w f g M N)
    (g : (S).orth (K₁ y)=0) (q : inner ℂ (K₁ x) ((S).E Δ (K₁ y)) ≠0) :
    _root_.YM.SatinMacro.Ticket (skyline Y H V Q Qc C 3 χ U) (K₁ x) (K₁ y)
      (e· p') Δ := by
  have hc:= Relief.analyt_h Y H V Q Qc C L χ U p' (κ x) (κ y) h.scope (Sable.pulsed Λ s)
    Δ (MeshClock.each ..)
  have he: inner ℂ (K₁ x) ((S).U 0 ((S).E Δ (K₁ y)))= _ :=
    congrArg (inner ℂ (K₁ x)) (DFunLike.congr_fun (S).uZero ((S).E Δ (K₁ y)))
  exact ⟨he.trans_ne q, Relief.padding Y H V Q Qc C L χ U s y,g,-(Sable.door Λ s),neg_lt_zero.mpr (Sable.pulsed Λ s),hc⟩

local notation "pose" p:max u:max t:max=> Θ' ((u:ℝ) • (Relief.aim 3 p)) (t:ℝ)
variable {x y z:Tower.Field Y H s 3 0 false} {A A':Actress.Label Y H 3 false}
    (h : Fierce Y H V Q Qc C s X F G χ U x₀ x y z A A')
include h
lemma Fierce.ticket : _root_.YM.SatinMacro.Ticket (skyline Y H V Q Qc C 3 χ U) (K₁ x) (K₁ y) (aim 3 p') Δ :=
  Library.ticket Y H V Q Qc C s χ U p' x y h.campus.thermal h.polar.1 (norm_pos_iff.mp (Torrent.fare_p.trans h.neve))

local notation "𝔉" a:max => worldShelf Y H V Q Qc C L χ U (a,0)
local notation "Λw" => marks (timeMesh Λ)

/-- Transversal stamps arbitrarily far! any positive spatial axis. Failure even
without using heat itself as either operator. Thus no locality by declaring these
observables local in ANY bounded set (from their finite EUCLIDEAN regions or
otherwise), even at one observing resolution, when retaining actual width
prescription vectors and actual spacetime translations. Tested with the
adjoint too (no claim about mutual commutation when not taking adjoints).
The real times can be requested in any nonempty open interval.
-/
theorem Fierce.width_pair_fails (X₁ X₂:Set E4) (a:IsBounded X₁)(b:IsBounded X₂)
    (A₁ A₂ : ((Polaris Y H V Q Qc 3 false (C 3) U).Realm (look 3)).Op)
    (r:A₁ Ω=K₁ x)(r': A₂ Ω=K₁ y) {t t':ℝ}(w:t<t') :
    ∃ᶠ u:ℝ in atTop, u ∈ Λw ∧ (∀ d∈ Set.Icc t t',
      _root_.YM.SatinMacro.Apart X₁ (_root_.YM.SatinMacro.there (pose p' u d) X₂)) ∧
      (∃ d∈ Set.Ioo t t', ¬ Commute (star A₁) (_root_.YM.SatinMacro.act (σ) (pose p' u d) A₂)) :=
  _root_.YM.SatinMacro.Ticket.distinct (h.ticket Y H V Q Qc C s X F G χ U x₀ p')
    ((show 0 < (1:ℝ) from zero_lt_one).trans_eq (aim_length 3 p').symm)
    (daylight (timeMesh Λ)) X₁ X₂ a b w A₁ A₂ (Ω) (skyline_static Y H V Q Qc C χ U) r r'

/-- In particular, at the two labels themselves, on *that* character and sector. -/
theorem Fierce.width_pair_noncommutes (X₁ X₂:Set E4) (a:IsBounded X₁)(b:IsBounded X₂) {t t':ℝ}(w:t<t') :
    ∃ᶠ u:ℝ in atTop, u ∈ Λw ∧ (∀ d∈ Set.Icc t t',
      _root_.YM.SatinMacro.Apart X₁ (_root_.YM.SatinMacro.there (pose p' u d) X₂)) ∧
      (∃ d∈ Set.Ioo t t', ¬ Commute (star (𝔉 A)) (_root_.YM.SatinMacro.act (σ) (pose p' u d) (𝔉 A'))) :=
  Fierce.width_pair_fails Y H V Q Qc C s X F G χ U x₀ p' h X₁ X₂ a b (𝔉 A) (𝔉 A')
    h.campus.fly.2.2.1 h.campus.sail_.2.2.1 w
end Mills
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Mills
#print axioms Fierce.ticket
#print axioms Fierce.width_pair_noncommutes
