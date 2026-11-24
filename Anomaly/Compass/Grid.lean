import Anomaly.Compass.Move
import Anomaly.Compass.Love
import Anomaly.Compass.Ices
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
open Oise Rive
open Ione.Clock
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Tc"=> mid N B
local notation "Tf"=> mid P B
local notation "Wν" => (duty_Q X.p.order X.p.power*W)
-- CP protocol reports.
variable {j k mc:ℕ}
variable {r:I→Site (mid N B)}{A:I→ArcΦ}{a:I→ℝ}{X₁:Key I→RegBudget (mid P B)}{X₂:Key I→ForceBudget (mid P B)}
structure Reception (r:I→ Site (mid N B))(M:Key I→RegBudget (mid P B))(F:Key I→ForceBudget (mid P B))(Z:I→ArcΦ)(u:I→ℝ)(n:ℕ) (E:Key I→RegBudget (mid N B))(Pv:Key I→ForceBudget (mid N B))(t:I→ℂ)(c:I→ArcΦ) :Prop where
   power : Cause_P V P_ G S G₀ G₁ X Y M 0 F Xp q d h Vp Vf r u Z E Pv c t T (duty_Q X.p.order X.p.power*W) C BQ Rt Zt κp
   flags : ∀ z∈hill I,FlagWidth X.p (Pv z) n
   thought:∃ Yb Y', Diesel X.p (Cube.node∘r) h κp Vp Yb Y' E (α_ξ t)
-- layout possibly repeated roles. Hosts with extra unused labels. Always specific prototype.
structure Scrutiny (i:J→I)(s:J→Sweep (mid N B))(r:I→Site (mid N B))(σ:J→Site (mid N B))(X₁:Key I→RegBudget (mid P B))(X₂:Key I→ForceBudget (mid P B))(V₁:Key J→RegBudget (mid P B))(V₂:Key J→ForceBudget (mid P B)): Prop where
   ride (j:J): s j∈Whirl (mid N B)
   path (j:J): mPath (s j) (σ j)=r (i j)
   park(j:J): passingR (mid P B) (reSweep G (s j)) (νTip X₁ (i j)) (νTip V₁ j)
   fire(j:J): passingF (mid P B) (reSweep G (s j)) (emberTip X₂ (i j)) (emberTip V₂ j)
-- shadow namespace Ra
abbrev orbit (Φ:I→ArcΦ) (i:J→I)(s:J→Sweep (mid N B)) :=fun j=> arc_s (s j).s (Levier.spinU false (s j).s) (Φ (i j)) -- explicit
abbrev paint_S (t:I→ℂ)(i:J→I)(s:J→Sweep (mid N B)) := fun j=> Spire.payZ (s j) (t (i j))
variable {n₀:ℕ}
structure RoadMap (r:I→Site (mid N B))(X₁:Key I→RegBudget (mid P B))(X₂:Key I→ForceBudget (mid P B))(A:I→ArcΦ)(a:I→ℝ)(n mc:ℕ)
   (F:Key I→RegBudget (mid N B))(P_F:Key I→ForceBudget (mid N B))(t:I→ℂ)(c:I→ArcΦ):Prop where
   receipts: Reception V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt κp r X₁ X₂ A a n F P_F t c
   begs: ∀ {J:Type}[LinearOrder J][Fintype J](i:J→I)(s:J→Sweep (mid N B))(σ:J→Site (mid N B))(Z:Key J→RegBudget (mid P B))(V':Key J→ForceBudget (mid P B)),
     Scrutiny G i s r σ X₁ X₂ Z V' →OrbitPulse G X Y h b g l.L σ Z V' (orbit A i s) (a∘i) mc →∃ Y₀ Pv, Reception V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt κp σ Z V' (orbit A i s) (a∘i) n Y₀ Pv (paint_S t i s) (orbit c i s) ∧ ∀ j, νTip Y₀ j=dashF (s j) (νTip F (i j)) ∧ passingF (mid N B) (s j) (emberTip P_F (i j)) (emberTip Pv j)

variable {L0:ℕ}{P0:BudgetPoint}{z a' b₁ c₁:ℝ}{o:Site (mid N B)} {E:Copy (mid N B)}{A0:RegBudget (mid N B)}{V':Cusp (mid N B)}{t:ℂ}{Φ:ArcΦ}
lemma Ice_γ (x:0≤z) (U:Ice L0 o P0 z a' b₁ c₁ E A0 V' t Φ): 0≤a' ∧ 0≤b₁:=by
 constructor
 · obtain ⟨W,u,H⟩:=U.axle.vest.weight; refine le_trans ?_ (H (node o)); apply sum_nonneg; intro i _; split_ifs; refine mul_nonneg (Real.exp_pos _).le (Roots.gradeE _ _ (u i) x); rfl
 obtain ⟨K,g,p,h⟩:=U.grant; refine le_trans ?_ (p (node o)); unfold tallB; exact sum_nonneg fun i _=>mul_nonneg (g.1 i) (Real.exp_pos _).le
lemma iceφ_grow (x:0≤z) (U:Ice L0 o P0 z a' b₁ c₁ E A0 V' t Φ)(D:P0.order=6)(v:P0.power=2) : Ice L0 o P0 z (duty_Q P0.order P0.power*a') (strive_E P0.order*b₁) c₁ E A0 V' t Φ:=by
 obtain ⟨p,w⟩:= Ice_γ x U; apply U.gain_μ
 · apply le_mul_of_one_le_left p; unfold duty_Q composeCost; rw [D,v]; norm_num [Nat.factorial]
 · apply le_mul_of_one_le_left w; unfold strive_E composeCost; rw [D]; norm_num [Nat.factorial]
 rfl
end YM.CF.QuadClock
