import Anomaly.Second.Meter
import Anomaly.Apert.Sync
/-! framed representation of first accounts, including exposures on all REAL pins. (phase separately via payZ.) -/
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
variable {r:I→Site (mid N B)}{σ:J→Site (mid N B)}{A:I→ArcΦ}{Y₁:Y.p.supportExponent = 1} {Φ:J→ArcΦ}{a:I→ℝ}{t:J→ℝ}{mc:ℕ}
variable {X₁:Key I→RegBudget (mid P B)}{Xz:Key I→ForceBudget (mid P B)}{Y₂:Key J→RegBudget (mid P B)}{Yz:Key J→ForceBudget (mid P B)}
variable (U:OrbitPulse G X Y h b g l.L r X₁ Xz A a mc)(R:OrbitPulse G X Y h b g l.L σ Y₂ Yz Φ t mc)
variable (s:Sweep (mid N B))(i:I)(j:J)
local notation "Ωσ"=> reSweep G s
variable(hY:passingR (mid P B) (reSweep G s) Y.F Y.F)(hX:passingF (mid P B) (reSweep G s) Y.K Y.K)
variable(hV:passingR (mid P B) (reSweep G s) (νTip X₁ i) (νTip Y₂ j)) (hU:passingF (mid P B) (reSweep G s) (emberTip Xz i) (emberTip Yz j))
variable {Be:Observatory G X.p}{X₀: Key I→Cusp (mid N B)} {D: Key J→ Cusp (mid N B)}
variable (pX:∀ z∈hill I,Be.source (X₁ z) (Xz z) (X₀ z)) (pG:∀ z∈hill J,Be.source (Y₂ z) (Yz z) (D z))
   (v₁:∀ i x,River (fun z=> heat_P X.p X₀ z i x)) (v₂:∀ i x,River (fun z=> heat_P X.p D z i x))
include U R hY hX hV hU pX pG
lemma pinsAgree (x:ℝ)(p:|x|≤1) : MirrorBill (mid N B) X.p s (X₀ (realKey i x)) (D (realKey j x)):=by
 apply Be.flies s (X₁ _) (Y₂ _) (Xz _) (Yz _) _ _ (pX _ (realKey_mem _ x p)) (pG _ (realKey_mem _ x p))
 · rw [U.north i x p,R.north j x p,U.buy.rail.1,R.buy.rail.1]; exact hY.add Ωσ (hV.smul Ωσ x)
 rw [U.south i x p,R.south j x p,U.buy.rail.2.2,R.buy.rail.2.2]; exact hX.add Ωσ (hU.smul Ωσ x)
include v₁ v₂
lemma listens (W:Orbit (mid N B)): feeTip X.p D j (yellA s W)= suit_Y s (feeTip X.p X₀ i W):=by
 let ht:= pinsAgree G X Y h b g U R s i j hY hX hV hU pX pG -- syntax args check
 have hy:passingFee (mid N B) s (opTip (heat_P X.p X₀) i) (opTip (heat_P X.p D) j):=by
    intro k U; let q0:=fun z:Key I=> heat_P X.p X₀ z k U; let q1:=fun z:Key J=>heat_P X.p D z (moldA s k) (yellA s U)
    have hg:= turnAxis s i j q0 q1 (v₁ _ _) (v₂ _ _) 1 (fun x p=> ?_); · exact (one_smul ..).symm.trans hg
    unfold q0 q1; rw [mul_one]; simp only [heat_P,Pi.sub_apply,map_sub]; rw [(ht x p).wax k U]
    have hz: realKey i 0=0:=by simp only [realKey,Complex.ofReal_zero,Mew.centre]
    have hz':realKey j 0=0:=by simp only [realKey,Complex.ofReal_zero,Mew.centre]
    have hr:=(ht 0 (by norm_num)).wax k U; rw [hz,hz'] at hr; rw [hr]
 unfold feeTip coldE; rw [map_sum]; symm; refine sum_equiv (moldA s) (fun a=>?_) (fun a _=>(hy a W).symm)
 simp only [mem_filter,mem_univ,true_and]; exact (Salt.glowA ..).symm

local notation "Kf" V:max Y₀:max B:max=> fun z=> rust_L X.p (Y₀ z) (V+Φstack B z)
omit v₁ v₂ U R hY hX hV hU pX pG
private lemma vibeStack(A:I→Cusp Tc)(v:ℝ)(i:I): Φstack A (realKey i v)= v • A i:=by unfold Φstack; rw [Finset.sum_eq_single i,realKey,update_self]; rfl; intro k _ u; unfold realKey; rw [update_of_ne u]; exact zero_smul ..; simp -- tune include h variables
include U R hY hX hV hU pX pG
lemma listenForce (G_:Cusp (mid N B))(g':ZealQ G_)(A₀:I→Cusp (mid N B))(A₁:J→Cusp (mid N B))(v:passingU_n (mid N B) s (A₀ i) (A₁ j)) (p:∀ i x,River (fun z=>(Kf G_ X₀ A₀) z i x))(u:∀ i x,River (fun z=>(Kf G_ D A₁) z i x)): passingF (mid N B) s (emberTip (Kf G_ X₀ A₀) i) (emberTip (Kf G_ D A₁) j):=by
 intro Q F k; let L:= Kf G_ X₀ A₀; let M:= Kf G_ D A₁
 let ht:=pinsAgree G X Y h b g U R s i j hY hX hV hU pX pG
 have hv:=turnAxis s i j _ _ (p Q F) (u (moveForce s Q) (yellA s F)) 1 (fun x p=>?_); · exact (one_smul ..).symm.trans hv
 rw [mul_one]; apply (ht _ p).lamp _ _ _ Q F k
 rw [vibeStack,vibeStack]; exact (show passingU_n (mid N B) s G_ G_ from (fun j x i k v t=>g' s x i j k v t)).add s (v.smul s x)
end YM.CF.QuadClock
