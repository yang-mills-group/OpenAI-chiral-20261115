import SatinThinDisclosedSatin
import YM.SU5.FiniteGaugeData.Azure.Finale

/-!
# The native Azure probes on the selected Satin experiment

The two submissions can use the same preparation, course and unselected history
through the fields of `Spine`. Restricting the selected reading to the native
observable algebra preserves raw values and products. The finite insertions
certified by `FullPrismLab` are nevertheless genuinely mixed. In particular
neither insertion can be the literal gauge-native first operand of `Lodged`.
-/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 350000
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
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight

namespace Spine

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

/-- Forget the extra native covariance certificate while retaining the identical raw family. -/
def azureNativeInclusion (P : Spine) : Charm.W P.calibration →ₐ[ℂ] P.Test where
  toFun w := ⟨w.val, w.property.1⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem azureNativeInclusion_val (P : Spine) (w : Charm.W P.calibration) :
    (P.azureNativeInclusion w).val = w.val := rfl

/-- A choice for the functional argument of the Azure interface, on the specified Satin character. -/
def azureReadingOnSelectedVacuum (P : Spine) (x : P.Spectrum0 3) (s : ℕ) :
    Charm.W P.calibration →ₗ[ℂ] ℂ :=
  (P.singleState 3 s x).comp (P.azureNativeInclusion.toLinearMap)

theorem azureReadingOnSelectedVacuum_mul (P : Spine) (x : P.Spectrum0 3) (s : ℕ)
    (u v : Charm.W P.calibration) :
    P.azureReadingOnSelectedVacuum x s (u * v) =
      P.singleState 3 s x (P.azureNativeInclusion u * P.azureNativeInclusion v) := by
  change P.singleState 3 s x (P.azureNativeInclusion (u * v)) = _
  rw [map_mul]

/-- The Azure centered joint reading is the centered reading of the very same
character on the two included native observables. -/
theorem azureBeaconOnSelectedVacuum (P : Spine) (x : P.Spectrum0 3) (s : ℕ)
    (u v : Charm.W P.calibration) :
    _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Prato.Beacon
        P.run P.large (P.azureReadingOnSelectedVacuum x s) u v =
      P.singleState 3 s x (P.azureNativeInclusion u * P.azureNativeInclusion v) -
        P.singleState 3 s x (P.azureNativeInclusion u) *
        P.singleState 3 s x (P.azureNativeInclusion v) := by
  change P.singleState 3 s x (P.azureNativeInclusion (u * v)) -
    P.singleState 3 s x (P.azureNativeInclusion u) * P.singleState 3 s x (P.azureNativeInclusion v) = _
  rw [map_mul]

/-- Every actual smeared Satin insertion is durable, so it can be presented in
Azure's native algebra without changing the stencil, the test function or its support. -/
def azurePrepared (P : Spine) (t : ℕ) (B : P.Apron) (F : SampleDose) :
    Charm.W P.calibration :=
  ⟨(P.prepared t B F).val, (P.prepared t B F).property,
    (enclave_spec P.calibration).mp (P.prepared_color t B F)⟩

@[simp] theorem azureNativeInclusion_prepared (P : Spine) (t : ℕ)
    (B : P.Apron) (F : SampleDose) :
    P.azureNativeInclusion (P.azurePrepared t B F) = P.prepared t B F := rfl

/-- The literal finite support certificate is also a native Azure locator. -/
theorem azurePrepared_at (P : Spine) (t : ℕ) (B : P.Apron) (F : SampleDose) (ht : B.s ≤ t) :
    ∃ S : Finset Cover, Charm.Locator P.calibration (P.azurePrepared t B F) S ∧
      P.pinFoot t S ⊆ P.spacePrice B F :=
  P.prepared_at t B F ht

theorem azureBeaconOnPrepared (P : Spine) (x : P.Spectrum0 3) (t : ℕ)
    (B C : P.Apron) (F U : SampleDose) :
    _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Prato.Beacon
        P.run P.large (P.azureReadingOnSelectedVacuum x t)
        (P.azurePrepared t B F) (P.azurePrepared t C U) =
      P.singleState 3 t x (P.prepared t B F * P.prepared t C U) -
        P.singleState 3 t x (P.prepared t B F) * P.singleState 3 t x (P.prepared t C U) :=
  P.azureBeaconOnSelectedVacuum x t _ _

theorem azureNativeGauge_is_pure (P : Spine) (u : Charm.W P.calibration)
    (hu : Verne.GNative P.calibration u) :
    Six.PureGauge P.calibration (P.azureNativeInclusion u) := by
  obtain ⟨F, S, hF, rfl⟩ := hu
  refine ⟨S, shiftW false F hF, ?_, rfl⟩
  apply shift_loc

theorem azureNativeMatter_is_pure (P : Spine) (u : Charm.W P.calibration)
    (hu : Verne.MNative P.calibration u) :
    Six.PureMatter P.calibration (P.azureNativeInclusion u) := hu

theorem mixed_ne_azure_gauge_raw (P : Spine) {z : P.Test} (hz : P.reallyMixed z)
    (u : Charm.W P.calibration) (hu : Verne.GNative P.calibration u) :
    z.val ≠ u.val := by
  intro eq
  have same : z = P.azureNativeInclusion u := Subtype.ext eq
  apply hz
  left
  rw [same]
  exact P.azureNativeGauge_is_pure u hu

theorem mixed_ne_azure_matter_raw (P : Spine) {z : P.Test} (hz : P.reallyMixed z)
    (u : Charm.W P.calibration) (hu : Verne.MNative P.calibration u) :
    z.val ≠ u.val := by
  intro eq
  have same : z = P.azureNativeInclusion u := Subtype.ext eq
  apply hz
  right
  rw [same]
  exact P.azureNativeMatter_is_pure u hu

variable (P : Spine) (x : P.Spectrum0 3)
variable (A : ℕ → P.Apron) (c r n : ℕ → ℕ) (w : Lead.Clan → Prism)
variable (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
variable (g h : ℕ) (T' : P.HandleWith x c r A n) (F U : SampleDose)
variable {C L : Doorway} {s k : ℕ} {K' : P.Register} {μ : ℝ}

/-- The full centered six-by-six joint reading in Azure's native algebra on the
same character, smears and reflected stencils used in the disclosed experiment. -/
def azurePrism (i t : ℕ) : CrossRead :=
  Matrix.of fun a b : Lead.Clan =>
    _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Prato.Beacon
      P.run P.large (P.azureReadingOnSelectedVacuum x t)
      (P.azurePrepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F)
      (P.azurePrepared t ((P.soldTrumpet A c r n w) b i) U)

/-- The two native representatives have actual finite locators inside the very
same earlier and later physical boxes used for the thin limit. -/
theorem fullPrism_azure_boxes
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a b : Lead.Clan,
      ∃ S Q : Finset Cover,
        Charm.Locator P.calibration (P.azurePrepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F) S ∧
        Charm.Locator P.calibration (P.azurePrepared t ((P.soldTrumpet A c r n w) b i) U) Q ∧
        P.pinFoot t S ⊆ C.invites ∧ P.pinFoot t Q ⊆ L.invites := by
  filter_upwards [D.under_boxes] with i inside
  intro t ht a b
  obtain ⟨S, locS, footS⟩ := P.azurePrepared_at t (((P.soldTrumpet A c r n w) a i).kiss P 3) F ht
  obtain ⟨Q, locQ, footQ⟩ := P.azurePrepared_at t ((P.soldTrumpet A c r n w) b i) U ht
  exact ⟨S, Q, locS, locQ, footS.trans (inside a).1, footQ.trans (inside b).2⟩

theorem fullPrism_azure_actual
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K')
    (i t : ℕ) (ht : c (n i) ≤ t) :
    P.azurePrism x A c r n w F U i t =
      P.reportPrism A c r n w F U i t (P.singleState 3 t x) := by
  funext a b
  change _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Prato.Beacon
    P.run P.large (P.azureReadingOnSelectedVacuum x t)
    (P.azurePrepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F)
    (P.azurePrepared t ((P.soldTrumpet A c r n w) b i) U) = _
  rw [P.azureBeaconOnPrepared, (D.then_read.bothZero a i t ht).1, zero_mul, sub_zero] <;> rfl

/-- At sufficiently fine consultations, the centered native matrix equals the
actual-minus-factorized matrix of the disclosed experiment, entry by entry. -/
theorem fullPrism_azure_comparison
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t →
      P.azurePrism x A c r n w F U i t =
        P.reportPrism A c r n w F U i t (P.singleState 3 t x) -
        P.reportPrism A c r n w F U i t (P.thinSplit x t) := by
  filter_upwards [D.then_read.comparison] with i split
  intro t ht
  rw [(split t ht).2, sub_zero]
  exact P.fullPrism_azure_actual x A c r n w V g h T' F U D i t ht

theorem fullPrism_azure_margin
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w μ F U) d ∧
      ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d := by
  obtain ⟨d, hd, limit, _, finite⟩ := D.margin
  refine ⟨d, hd, limit, ?_⟩
  filter_upwards [P.fullPrism_azure_comparison x A c r n w V g h T' F U D, finite] with i same bound
  intro t ht
  rw [same t ht]
  exact bound t ht

theorem fullPrism_azure_limits
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    (∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
      (𝓝 (P.thinJournal x A c r n w T' F U i))) ∧
    Tendsto (P.thinJournal x A c r n w T' F U) atTop (𝓝 (P.readPrism x V w μ F U)) := by
  refine ⟨?_, D.final_limit⟩
  filter_upwards [D.first_limit, P.fullPrism_azure_comparison x A c r n w V g h T' F U D] with i first same
  apply first.congr'
  filter_upwards [eventually_ge_atTop (c (n i))] with t ht
  exact (same t ht).symm

/-- On the actual two smeared families in the disclosed experiment, the necessary
gauge-native first-operand condition fails in either order at every sufficiently
fine consultation. This concerns equality of raw families at those consultations. -/
theorem fullPrism_excludes_azure_gauge
    (D : P.FullPrismLab x A c r n w V g h T' μ F U C L s k K') :
    ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
      ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
        (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
        (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val := by
  filter_upwards [P.verified_mixtures x A c r n w V g h T' F U D] with i mix
  intro t ht a u hu
  obtain ⟨left, right⟩ := mix t ht a
  exact ⟨P.mixed_ne_azure_gauge_raw left u hu, P.mixed_ne_azure_gauge_raw right u hu⟩

/-- Apply the exclusion to CP18's disclosed, normalized, separated experiment
on its chosen character. The fixed probe functions and both original boxes are
retained, together with the thin-field theorem on precisely those witnesses. -/
theorem exists_disclosed_satin_native_contrast :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
      (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
      Experiment P K c r x R ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
      tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
      P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U ∧
      ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
        (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
        (g h : ℕ) (X : P.HandleWith x c r A n),
        P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox
          (c i₀) (r i₀) K ∧
        (∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d) ∧
        ((∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
          (𝓝 (P.thinJournal x A c r n w X F U i))) ∧
          Tendsto (P.thinJournal x A c r n w X F U) atTop (𝓝 (P.readPrism x V w 1 F U))) ∧
        ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
          ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
            (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
            (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val := by
  obtain ⟨P, K, _, beta, c, r, x, R, _, experiment, transmission, _, i₀,
    F, U, normF, normU, boxF, boxU, six, fixedRead, g, h, v, a, hv, q, V,
    n, X, w, lab, _, _⟩ := disclosed_satin_witness
  let A := P.cinema x g h v a q hv
  exact ⟨P, K, c, r, x, R, i₀, F, U, beta, experiment, transmission, normF,
    normU, boxF, boxU, six, fixedRead, A, n, w, V, g, h, X, lab,
    P.fullPrism_azure_margin x A c r n w V g h X F U lab,
    P.fullPrism_azure_limits x A c r n w V g h X F U lab,
    P.fullPrism_excludes_azure_gauge x A c r n w V g h X F U lab⟩

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
