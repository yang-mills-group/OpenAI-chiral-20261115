import Anomaly.Compass.Grid
import Anomaly.Compass.Card
import SatinThinVow
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
variable (p:JuiceMeter V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp j mc) (U:OrbitPulse G X Y h b g l.L r X₁ X₂ A a mc)
local notation "Meter"=>JuiceMeter
-- Ψ ι horizon symmetry.
include U p
lemma frame_Bill (hc:IncX primeU Y.F Y.p h 1)(u₁:X.p.order=6)(u₂:X.p.power=2):∃ F E t0 Φ,
 RoadMap V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp r X₁ X₂ A a j mc F E t0 Φ:=by -- '_' shadow h rename
 obtain ⟨Be,Vκ,Ca,Bm⟩:= p.trust; obtain ⟨F,v,s,u,T'⟩:=Bm.heat r X₁ X₂ A a U
 choose E K z Φ H using u
 obtain ⟨R,hX,z',t,q,Q⟩:=T' E K Φ z (fun i=> ⟨iceφ_grow (zero_le_one.trans p.toe) (H i).1 u₁ u₂,(H i).2⟩)
 obtain ⟨M₀,Γ,θ⟩:=vow_life Y h hc p.toe (fun i _=>p.stillE i)
 let Xk:= fun i=> rust_L X.p (F i) (Vκ+Φstack K i)
 refine ⟨R,Xk,z,Φ,⟨⟨hX,z',_,_,Q⟩,?_⟩⟩
 intro J _ _ i S₁ σ E' K' w R'
 obtain ⟨N,Pz,T',_,Tκ⟩:=Bm.heat _ _ _ _ _ R'
 let B₁:=fun j:J=> dashF (S₁ j) (E (i j)); let F₁:= fun j:J=>dashK (S₁ j) (K (i j))
 let θ₁(j:J):=Φ (i j); let z₁:=paint_S z i S₁; let θ':=orbit Φ i S₁
 obtain ⟨A₀,hT,b₀,Jv,M,Q⟩:= Tκ B₁ F₁ θ' z₁ (fun k=>by
   intro Kμ ℝq; let j:=i k; let s':=S₁ k; let e:=h
   let D:= H j; let T₀:= s'.s; let t' := spinU false T₀; let η:ArcΦ:=arc_s T₀ t' (A j)
   let u:=w.ride k; let Yv:= X.p; let U:=U; have hw:Kμ=(M₀:ℂ):= Γ _
   let b':=H j|>.1; let ht':=p.toe
   have hv := stocks (Q:=A j) (Q':=Φ j) s' u t' (show αPrice l.L _ _ _ _ _ _ _ _ X.p Y.p (M₀:ℂ) from (Γ _) ▸ D.2) -- pattern infer.L.V.Pin/Wager
   have had:= listens G X Y h b g U R' s' j k (p.stillE _) (p.stillF _) (w.park k) (w.fire k) v Pz s T'
   let q':= p.chamber
   -- move annot.
   let k_:= κprobe mintR l.L h (a j) T (nun_ω Y.F (Hove.heel G (r j))) (A j)
   have kK:s'=S₁ k:=rfl
   have he: k_=ℝq:=by
      unfold k_ ℝq; rw [Γ (Hove.heel G (r j)),hw]; exact Eq.symm (sameGauge ..)
   obtain ⟨e1,e2,e3⟩:= aria t' T₀ (A j)
   have heM:=Bm.voyage η (A j) e1 e2 e3
   have hi:=iceLaw s' (σ k) (feeTip X.p _ j) (feeTip X.p _ k) _ _ _ _ (W*k_) (Ca (A j) (a j)) _ (zero_le_one.trans p.toe) (Ice_γ (zero_le_one.trans p.toe) b').1 (show Ice l.L.val (mPath (S₁ k) (σ k)) X.p h (W*k_) (Ca (A j) (a j)) (C*k_) (feeTip X.p F j) (E j) (K j) (z j) (Φ j) from by rw [w.path k]; exact b') q'.rooms q'.period u t' (spinZ ..) had
   rw [he,← heM] at hi; exact ⟨hi,hw.symm ▸ hv⟩)
 refine ⟨A₀,_,⟨hT,b₀,_,_,Q⟩, fun j=>⟨?_,?_⟩⟩
 · rw [Jv,t]; try rfl
 exact listenForce G X Y _ b g U R' _ (i j) j (p.stillE _) (p.stillF _) (w.park j) (w.fire j) v Pz Vκ Bm.light K F₁ (fun i g _ D h f=> dash_apply (S₁ j) ..) (fun i v=>(hX.tape i).2 v) (fun i v=>(hT.tape i).2 v)
end YM.CF.QuadClock
