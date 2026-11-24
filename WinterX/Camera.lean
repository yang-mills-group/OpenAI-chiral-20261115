import WinterX.Instrument
import WinterX.Pantry
import YM.CF.Fans.Cause
import Thin.CapsEarn
import YM.CF.Fans.Elm

/- Adapted from YM/CF/Fans/Elm.lean for the NoSlip, capped ScaledV use below. -/
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z gg A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open Neon Mew Vow Tap Rive Bake Larch Salt Ione Sour Moto
open scoped Mew
open Both
-- Feynman transfer interface. γΓ is κPass. Key submission at fine Y $f/g/r. inputs.Xo offset. exact stage backend same for all. capacities flexible via callers. Expose Stage$ device per submission as existential with commitments obeying simultaneous comparison through same equivalence; can `Classical.choose` based solely on inputs, no future Pledge.
variable {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q:Chi}
local notation "Nk"=> mid N B
local notation "Pk"=> mid P B
variable (Wξ:Op SU.Slot)(v1 kF Wκ Δ_ f0 g0 g1 g2 Q₁ Q₂ Q₃ cΦ Zμ:ℝ)
variable (price_R:ℝ→ℝ)(θc:ℝ)(gK:ℕ)
variable {J:Type}[LinearOrder J][Fintype J]{h Kv Zv:ℝ}(ζP:J→Site (mid N B))(E' S':Key J → RegBudget (mid P B))(Yf:Key J→ ForceBudget (mid P B))(A_:J→ ArcΦ)(Dϕ:J→ℝ)
local notation "σ_p" => (Cube.node ∘ Hove.heel G ∘ ζP)
-- returns oracle.Binder ABI. Fintype & LOrder for LabelΩ need avoid instance paths.
abbrev capture (J:Type)[LinearOrder J] [Fintype J] (s:Side) := Key J →RegBudget s
abbrev attach (J:Type)[LinearOrder J][Fintype J](s:Side):= Key J→ ForceBudget s
def sees (u:Sweep (mid P B)) {I T:Type}[LinearOrder I][Fintype I][LinearOrder T][Fintype T](F S:capture I (mid P B))(K:attach I (mid P B))(x:Key I)
    (F' S':capture T (mid P B))(K':attach T (mid P B))(y:Key T):Prop:=
 (∀ (j:Scree.Hub (mid P B))(V:Pane (mid P B)),F' y (moveHub u j) (Spire.flashA u V)= Ione.suit_Y u (F x j V)) ∧
 (∀ (j:Scree.Hub (mid P B))(V:Pane (mid P B)),S' y (moveHub u j) (Spire.flashA u V)=Ione.suit_Y u (S x j V)) ∧
 Both.ForceR u (K x) (K' y)
variable {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{χ:Chi}(u0 h:ℝ)
structure Hourly (V:Grace K R L)(U:Grasp V.U B d)(X: GramM (mid N B))(Y:GramM (mid P B))(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(Wξ:Op SU.Slot)(χ:Chi)
    (u0 h v1 kF Wκ Δ_ f0 g0 g1 g2 Zμ f g w Qκ θc:ℝ)(gK:ℕ)(AΦ:Cusp (mid N B)→Cusp (mid N B))(Kc:Cusp (mid N B))(γt:ℝ)
    (Clock:∀ (J:Type)[LinearOrder J][Fintype J],(J→Site (mid N B))→capture J (mid P B)→capture J (mid P B)→attach J (mid P B)→(J→ArcΦ)→(J→ℝ)→Key J→Cusp (mid N B)):Prop where
 zeal:ZealQ Kc
 crest :0≤Wκ
 hand (J:Type)[LinearOrder J][Fintype J](σ:J→Site (mid N B))(E Eo:capture J (mid P B))(F:attach J (mid P B))(Z:J→ArcΦ)(t:J→ℝ): MissionH Y h R.L G σ E Eo F Z t f g w Qκ →
    Soloing (S:=S) (G₀:=G₀) (G₁:=G₁) (kL:=u0) (q:=χ) (X:=X) (Y:=Y) (U:=U) (G:=G) (h:=h) V Wξ v1 kF Wκ Δ_ f0 g0 g1 g2 Zμ θc gK σ E Eo F Z t AΦ Kc γt (Clock J σ E Eo F Z t)
 compare (I T:Type)[LinearOrder I][Fintype I][LinearOrder T][Fintype T](σ:I→Site (mid N B))(E Eo:capture I (mid P B))(F:attach I (mid P B))(Z:I→ArcΦ)(t:I→ℝ)
    (σ':T→Site (mid N B))(M Mo:capture T (mid P B))(F':attach T (mid P B))(Z':T→ArcΦ)(t':T→ℝ):
    MissionH Y h R.L G σ E Eo F Z t f g w Qκ → MissionH Y h R.L G σ' M Mo F' Z' t' f g w Qκ →
    ∀ x∈hill I,∀ y∈hill T,∀ s:Sweep (mid N B), sees (B:=B) (P:=P) (reSweep G s) E Eo F x M Mo F' y → PotR s (Clock I σ E Eo F Z t x) (Clock T σ' M Mo F' Z' t' y)
structure Zodiac(V:Grace K R L)(U:Grasp V.U B d)(X:GramM (mid N B))(Y:GramM (mid P B))(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(Wξ:Op SU.Slot)(χ:Chi)(u0 h v1 kF Wκ Δ_ f0 g0 g1 g2 Zμ f g w Qκ:ℝ)(gK:ℕ):Prop where
 rate:Tune.qCorset X.p.threshold Y.p.threshold (R.L.val:ℝ) ≤ 4*(R.L.val:ℝ)⁻¹^4 ∧ (R.L.val:ℝ)⁻¹^4/4 ≤ Tune.qCorset X.p.threshold Y.p.threshold (R.L.val:ℝ)
 earns:∃ θ AΦ Kc γt Clock, Hourly V U X Y S G G₀ G₁ Wξ χ u0 h v1 kF Wκ Δ_ f0 g0 g1 g2 Zμ f g w Qκ θ gK AΦ Kc γt Clock
#check Hourly.compare
end YM.CF.Py
end
