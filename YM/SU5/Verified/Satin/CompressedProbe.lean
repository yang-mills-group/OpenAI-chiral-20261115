import YM.SU5.Verified.Satin.MixedLaw
/-! Carry the mixed single-observable reading through compression onto the joint
ground subspace. The unit vector here is the original invariant vector in that
subspace. An extremal component and multiplicativity of compressed products
require additional arguments. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
open Satin Tapestry
open Lifted (nodeC node_of)

open Buffered.Afterglow.Tower.SatinVerification

open Buffered.Afterglow.Tower Buffered.Afterglow.Tower.SlabMark
variable {i k : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Buffered.Family (tent Y H) → ℂ}
def mixed_in_ground (V : Universal Y H i k I E)
    (G : GroundExtension (i := i) (k := k) (E := E) Y H) (j : Axis)
    (room : Arena Y H G.history.circuit j 0 true) (q d w : ℕ) : Prop :=
  let Ω := Vacancy.seat0 Y H V G.history j true room
  ∀ z : SU.Slot, ∀ᶠ s in atTop, ∀ x : Cover,
    ∃ F : Vacancy.observable (tent Y H) true,
      F.val ∈ Filigree (tent Y H) (Window.family z) (booty x d q) (Sen x (payout d q w)) ∧
      Neutral (tent Y H) F.val ∧
      let reading := inner ℂ Ω ((Vacancy.cap Y H V s G.history G.clipped j true room F) Ω)
      reading = E s F.val ∧ 1 / 4 ≤ ‖reading‖

theorem ground_mixed_probes (V : Universal Y H i k I E)
    (G : GroundExtension (i := i) (k := k) (E := E) Y H) (j : Axis)
    (room : Arena Y H G.history.circuit j 0 true) {C Z : ℝ}
    (g : Cornet Y H q d w C Z) : mixed_in_ground Y H V G j room q d w := by
  intro z
  filter_upwards [certificate Y H C Z z g I E V] with s measured
  intro x
  obtain ⟨_, _, f, _, member, neutral, _, _, lower⟩ := measured x
  have test : TestFamily (tent Y H) true f := ⟨⟨_, (FilTest member).widen⟩, by simp⟩
  let F : Vacancy.observable (tent Y H) true := ⟨f, test, fun _ => neutral⟩
  have he := Vacancy.inspected (F := F) Y H V s G.history G.clipped j true room
  exact ⟨F, member, neutral, he, he.symm ▸ lower⟩

/-- An unconditional joint election, on all axes and all three pairs of matter slots. -/
theorem elected_ground_probes (ε η : ℝ) (small : 0 < η) :
    ∃ (P : Preparation) (l : ℕ), ε < P.x ∧ P.d ≤ η ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
    ∃ (H : Real.exp 1 ≤ P.x) (Y : Course P (VolumeCape.Dream.Nimbus l)) (q d w : ℕ)
      (a b : ℕ → ℕ) (I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ)
      (E : ℕ → Buffered.Family (tent Y H) → ℂ) (V : Universal Y H a b I E)
      (G : GroundExtension (i := a) (k := b) (E := E) Y H),
      ∀ j : Axis, ∃ room : Arena Y H G.history.circuit j 0 true,
        mixed_in_ground Y H V G j room q d w := by
  obtain ⟨P, l, Z, large, bound, nom, H, Y, q, d, w, C, g, a, b, I, E, V, ⟨G⟩, _⟩ :=
    mixed_law_with_ground ε η small
  refine ⟨P, l, large, bound, nom, H, Y, q, d, w, a, b, I, E, V, G, ?_⟩
  intro j
  obtain ⟨room⟩ := voyage_H Y H V G.history.circuit j 0 true
  exact ⟨room, ground_mixed_probes Y H V G j room g⟩
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.ground_mixed_probes
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.elected_ground_probes
