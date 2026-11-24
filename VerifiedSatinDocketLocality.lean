import YM.SU5.Macro.Censure
import YM.SU5.Macro.Together
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 1000000
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
  (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
open CF.Pannier.Chancel Tapestry Papal SatinVerification
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
open Crest.Airy (Coast Wq)
open Mileage
attribute [local instance] opCStarAlgebra
namespace Fern
open CF.Pannier.Chancel.Attic.Cairn CF.Pannier.Chancel.Attic.Cairn.Giant
open Planet Season
open Summer Summer.Mills Spectral Spectral.Alps Germ Germ.Alliance
variable {F:Rack Λ l}{Z:Clay Λ l}(e:Exhibition Y H i k I E F Z)
variable {A:Mezz}{b₀ v u' q d w:ℕ}{C₀ ε Γ δ:ℝ}{G H₁ H₂:Coast→ Wq A.marks}(L:Effigy Y H Γ b₀ v ε C₀ δ A u' G H₁ H₂)
variable (s n n' r:ℕ)(M:Giant)(Ψ:Horizon Y H V Q Qc 3 false (C 3))(x:Ψ.X)
    (X:SU.Slot→Family (tent Y H))(W:∀a:Window.Family,Bool→ Sermon A (tent Y H) a)
    (T: ∀ a:Window.Family,Bool→ SpireBook M (tent Y H) a) (P:Window.Family→ Voice.Tonic M)
local notation "T₀" a:max=> T a false
local notation "T₁" a:max=> T a true
local notation "χ"=> Ψ.character x
local notation "θ" j:max => escort Y H V Q Qc 3 false (C 3) j (C j) (Ψ.character x)
open Relief Bornology

/-- Spacelike noncommutation for two fixed labels on one specified realization. -/
def WidthCounterexample
    (U : Birthplace Y H V Q Qc 3 false (C 3) (θ 3))
    (left right : Actress.Label Y H 3 false) : Prop :=
      ∀ direction : Trans 3, ∀ first second : Set E4, IsBounded first → IsBounded second →
      ∀ t t' : ℝ, t < t' →
      ∃ᶠ u : ℝ in atTop, u ∈ marks (timeMesh Λ) ∧
        (∀ z ∈ Set.Icc t t', _root_.YM.SatinMacro.Apart first
          (_root_.YM.SatinMacro.there (_root_.YM.SatinMacro.joinST (u • Relief.aim 3 direction) z) second)) ∧
        (∃ z ∈ Set.Ioo t t', ¬ Commute
          (star (Summer.worldShelf Y H V Q Qc C 3 χ U (left, 0)))
          (_root_.YM.SatinMacro.act (Summer.skyline Y H V Q Qc C 3 χ U).unit
            (_root_.YM.SatinMacro.joinST (u • Relief.aim 3 direction) z)
            (Summer.worldShelf Y H V Q Qc C 3 χ U (right, 0))))

private theorem purchaseToWidth
    (family : Window.Family) (U : Birthplace Y H V Q Qc 3 false (C 3) (θ 3))
    (field₁ field₂ field₃ : Tower.Field Y H s 3 0 false)
    (left right : Actress.Label Y H 3 false)
    (pair : Summer.Mills.Fierce Y H V Q Qc C s M (T family false) (T family true)
      (Ψ.character x) U (P family) field₁ field₂ field₃ left right) :
    WidthCounterexample Y H V Q Qc C Ψ x U left right :=
  fun direction first second hfirst hsecond t t' htime =>
    @Summer.Mills.Fierce.width_pair_noncommutes Λ l Y H i k I E V D a b Q Qc C s M family
      (T family false) (T family true) (Ψ.character x) U (P family) direction
      field₁ field₂ field₃ left right pair first second hfirst hsecond t t' htime

/-- Fix the purchased character, then choose the realization and the two labels once.
    Their spacelike commutator fails for arbitrarily large transverse mesh translations. -/
theorem OnOrion.spacelikeWidthWitness
    (paid : OnOrion Y H V Q Qc C e L s n n' r M Ψ x X W T P q d w)
    (family : Window.Family) :
    ∃ U : Birthplace Y H V Q Qc 3 false (C 3) (θ 3),
    ∃ left right : Actress.Label Y H 3 false, WidthCounterexample Y H V Q Qc C Ψ x U left right := by
  obtain ⟨U, seat⟩ := @OnOrion.seats Λ l Y H i k I E V D a b Q Qc C F Z e A b₀ v u' C₀ ε Γ δ G H₁ H₂ L s n n' r M Ψ x X W T P q d w paid (3 : Axis)
  obtain ⟨field₁, field₂, field₃, left, right, pair⟩ := @OnOrion.docket Λ l Y H i k I E V D a b Q Qc C F Z e A b₀ v u' C₀ ε Γ δ G H₁ H₂ L s n n' r M Ψ x X W T P q d w paid U family
  exact ⟨U, left, right, purchaseToWidth Y H V Q Qc C s M Ψ x T P family U field₁ field₂ field₃ left right pair⟩

end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
#print axioms YM.CF.Buffered.Afterglow.Tower.Selection.Fern.OnOrion.spacelikeWidthWitness
