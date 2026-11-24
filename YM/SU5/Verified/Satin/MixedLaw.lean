import YM.SU5.Verified.Satin.GroundExtension
import YM.SU5.FiniteGaugeData.Pannier.Firmament
/-! Buy mixed probes and attach the joint ground projection on the very same Satin
readings. The lower bound is for the uncompressed readings, before selecting a sector. -/
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
theorem mixed_law_with_ground (ε η : ℝ) (small : 0 < η) :
    ∃ (P : Preparation) (l : ℕ) (Z : ℝ), ε < P.x ∧ P.d ≤ η ∧
      P.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H : Real.exp 1 ≤ P.x) (Y : Course P (VolumeCape.Dream.Nimbus l))
        (q d w : ℕ) (C : ℝ), Cornet Y H q d w C Z ∧
      ∃ (a b : ℕ → ℕ) (I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ)
        (E : ℕ → Buffered.Family (tent Y H) → ℂ),
        Universal Y H a b I E ∧ Nonempty (GroundExtension (i := a) (k := b) (E := E) Y H) ∧
        ∀ z : SU.Slot, ∀ᶠ s in atTop, ∀ x : Cover,
          (¬ CF.Pannier.Chancel.Parcel (tent Y H) (Window.family z)
            (booty x d q) (Sen x (payout d q w)) (E s)) ∧
          ∃ F : Buffered.Family (tent Y H),
            F ∈ Filigree (tent Y H) (Window.family z) (booty x d q) (Sen x (payout d q w)) ∧
            Neutral (tent Y H) F ∧ 1 / 4 ≤ ‖E s F‖ := by
  let supplier : Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
  obtain ⟨P, l, Z, large, bound, _, nom, H, Y, _, _, _, q, d, w, C, g,
    a, b, I, E, _, _, _, _, fashion, _⟩ := elite ε η small supplier
  let V := fashion.univ_
  refine ⟨P, l, Z, large, bound, nom, H, Y, q, d, w, C, g, a, b, I, E, V,
    extend_ground Y H V, ?_⟩
  intro z
  filter_upwards [Cornet.impression Y H C Z V z g, certificate Y H C Z z g I E V] with s fail measured
  intro x
  obtain ⟨_, _, F, _, member, neutral, _, _, lower⟩ := measured x
  exact ⟨fail x, F, member, neutral, lower⟩

end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.mixed_law_with_ground
