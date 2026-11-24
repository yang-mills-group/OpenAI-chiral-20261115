import YM.CF.BProof.Vac.Full
import YM.SU5.VerifiedPressure.FiniteGaugeData.Common
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}
open Bake PushA Episode Salt
variable {M:Side}{hx N0 n:ℕ}{T': Month x 1 6 2 N0 V W}
open Chaff Gloss Maize Tye RP RP.Str
open Brace
variable {F0:(m:Side)→Scroll m B (Brace.northZ m B)}
variable {J:Robes N V W}{η:ℝ}{b k Lm:ℕ} {A:FareFit R η}
open FareFit
namespace Patrol
variable (D:ForestDay V q h 1 6 2 N0 b Lm J F0 A T')
local notation "νγ"=>hat R.L x
local notation "Xκ"=> cell (M*N) B R.L
open Realm Realm.Shell Tide
variable {Z:Cape (M*N) B R.L}
open Vista Pitcher Pitcher.Estate
open BProof BProof.Estimator
namespace LoomKit
variable (M : Side) (P : LoomKit D M) (j : ℕ)
open Window.Unfit BProof Mint Chess BProof.Anthem
variable {A₀ : Diary.Prelude V γ} (X : Diary.Profile J A₀) (G : Life X x h)
  (E : Harbor M X x j) (hj : legal M X x j)
variable {r : ℕ} (Y : Bide.Half.ClockD R Lm J.n (Peaks.TripD.units R.L r))
  (yR : Peaks.TripD.SetK K.j R.L r) (u : Y.uF ≤ X.a)
variable {z₁ z₂ z₃ : ℝ} (S : ∀ e : Side, ScaleK z₁ z₂ (F0 e)) (vB : Phase.Budget B d z₃)
include X G E hj Y yR u S vB
/-- The original LoomKit constant follows on a nominated sequence once its
actual action and auxiliary law agree there, retaining the shared Grasp. -/
theorem on_same_history (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (act : ℕ → GramM (cell (M*N) B R.L j)) (law : ℕ → Scree.Loom (cell (M*N) B R.L j))
    (hg : ∀ᶠ n in atTop, act n = (((P.actual D M).run (σ n)).D j))
    (hl : ∀ᶠ n in atTop, law n = P.Z j) :
    ∀ᶠ n in atTop, price_vac (N:=N) (T':=T') M j ≤ ‖BPress.reading U (act n) (law n) 1‖ := by
  have h := hσ.tendsto_atTop.eventually (eventually_good D M P j X G E hj Y yR u S vB)
  filter_upwards [h,hg,hl] with n hn gn ln
  rw [gn,ln]
  exact hn
end LoomKit
end Patrol
end Cupboard
end YM.CF.Py
