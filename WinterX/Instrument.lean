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
abbrev κBill (Y:GramM (mid P B))(G:Ratio (mid N B) (mid P B))(L:Side)(Wκ:ℝ)(h:ℝ)(i:Site (mid N B))(Q:ℝ)(D:ArcΦ) := κprobe mintR L h Q Wκ (nun_ω Y.F (Hove.heel G i)) D
def MissionH (Y:GramM (mid P B))(h:ℝ)(L:Side)(G: Ratio (mid N B) (mid P B))(Ω:J→Site (mid N B))(A S:Key J→RegBudget (mid P B))(K:Key J→ForceBudget (mid P B))(F:J→ArcΦ)(D:J→ℝ)(f g w Qκ:ℝ):Prop:=
    (Call_H (Y:=Y) h A S K (Cube.node ∘ Hove.heel G ∘ Ω) f g w)∧(∀ j:J,Axon L.val (Hove.heel G (Ω j)) Y.p (νTip A j) h (D j) (F j)) ∧(∀ j:J,νTip S j=0)∧(∀ j:J,Sized_J (D j) Qκ (nun_ω Y.F (Hove.heel G (Ω j))) h (F j))∧∀ z∈hill J,S z=0
abbrev BoundsIce (Q:BudgetPoint)(L:ℕ)(p:Site (mid N B))(H A C u:ℝ)(r:Copy (mid N B))(F:RegBudget (mid N B))(K:Cusp (mid N B))(t:ℂ)(M:ArcΦ) :=Ice L p Q H A u C r F K t M
abbrev restoreF (P:BudgetPoint) (f:Cusp (mid N B)→Cusp (mid N B)) (Q:Cusp (mid N B))(F:Key J→Cusp (mid N B))(K:J→ Cusp (mid N B))(z:Key J):ForceBudget (mid N B):=budgetR (roomV P (Fex (f (F z))) (f (F z)) (Q+Φstack K z))
abbrev restoring (P:BudgetPoint)(f:Cusp (mid N B)→Cusp (mid N B))(F:Key J→Cusp (mid N B))(z:Key J):Pax (mid N B):= let W(z):= FeeD P (Fex (f (F z))); W z-W 0
abbrev icedCusp (P:BudgetPoint)(f:Cusp (mid N B)→Cusp (mid N B))(F:Key J→Cusp (mid N B))(i:J): Copy (mid N B):= coldE P (τι (restoring P f F) [i])
set_option maxHeartbeats 800000 in
def Soloing (f:Cusp (mid N B)→ Cusp (mid N B))(K0:Cusp (mid N B))(γp:ℝ)(F:Key J→ Cusp (mid N B)):Prop:=
 (∀ i∈hill J,PivotQual (n:=Nk) X.p h γp (F i) (f (F i)) f) ∧
 (∀ v:Aura Nk,∀ U:Orbit Nk,River (fun z:Key J=> restoring X.p f F z v U))∧
 (∀ i:J,
   let r:= κBill Y G R.L Wκ h (ζP i) (Dϕ i) (A_ i)
   ∃ (E0:RegBudget Nk)(Kv:Cusp Nk)(t:ℂ)(S0:ArcΦ),
        Ice R.L.val (ζP i) X.p h (Δ_*r) θc (f0*r) (icedCusp X.p f F i) E0 Kv t S0∧
        αPrice R.L h (Dϕ i) Wκ g0 g1 g2 (A_ i) S0 X.p Y.p (nun_ω Y.F (Hove.heel G (ζP i)))) ∧
 (∀ (ξ v:ℝ)(E0:J→RegBudget Nk)(Kv:J→Cusp Nk)(t:J→ℂ)(S0:J→ ArcΦ)(k:ℕ)(hc:0≤v)(hq: ↑k*v ≤ (gK:ℝ))
    (u:∀ i,
      let r:= κBill Y G R.L Wκ h (ζP i) (Dϕ i) (A_ i)
      Ice R.L.val (ζP i) X.p h (ξ*Δ_*r) (v*θc) (f0*r) (icedCusp X.p f F i) (E0 i) (Kv i) (t i) (S0 i)∧ αPrice R.L h (Dϕ i) Wκ g0 g1 g2 (A_ i) (S0 i) X.p Y.p (nun_ω Y.F (Hove.heel G (ζP i))))
    (p:GapN ζP X.p.B R.L.val k),
      ∃ (T:Key J→ RegBudget Nk), (∀ i:J,νTip T i=E0 i)∧ Cause_P V U G S G₀ G₁ X Y E' S' Yf Wξ q kL h v1 kF ζP Dϕ A_ T (restoreF X.p f K0 F Kv) S0 t Wκ (ξ * Δ_) f0 g0 g1 g2 Zμ)
-- notes: h, X variables implicit need in #check. uniform θ_E theory_e grant.First derivative tests.
#check Soloing
end YM.CF.Py
end
