import YM.SU5.Exchange.Force.Jets
import SatinThinRegister
import YM.SU5.Exchange.Force.Cloud
import SatinThinQuality
/-! Universal transmission estimate, real purchase. Replace Counsel, now full Arc shapes; include flag widths, motion along all Sweep (input comparison). Arbitrarily many
 aligned requests in the indicated markets. -/
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
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
local notation "TF"=> mid P B
local notation "Tc"=>mid N B

-- covers existence of purchases on base vs first tips on Mark arrays
open Oise Rive
structure AstroFunding (n m:ℕ):Prop where
 toe: 1 ≤ h
 hush: Y.slip=0
 stillE(s):passingR TF s Y.F Y.F
 stillF(s):passingF TF s Y.K Y.K
 shore: Foyer V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp m
 anchor: Arc_r Y h b b b
 chamber:HavenL Tc X.p l.L.val
 trust: ∃ (Be:Observatory G X.p)(Vκ:Cusp Tc)(Ca:ArcΦ→ℝ→ℝ), OrbitJet V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp Be Vκ Ca n m
lemma OrbitPulse.nil (F:Arc_r Y h b b b)(e:Y.slip=0)(n:ℕ)(U:Side): OrbitPulse G X Y h b g U Fin.elim0 (fun _=>Y.F) (fun _=>Y.K) (Fin.elim0) Fin.elim0 n:=by
 refine ⟨⟨⟨rfl,e.symm,rfl⟩,fun i=> ⟨fun _ _ _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>⟨zeroR _,zeroR _⟩⟩,fun i=> ⟨fun _ _ _ _ _=>rfl,fun _=>zeroR _⟩,fun v=>?_⟩, ?_,(fun i=> i.elim0),fun i=> i.elim0,fun i=> i.elim0,fun i=> i.elim0⟩
 · change Arc_r (color_b Y Y.beta Y.F 0 Y.K Y.v) _ _ _ _
   rw [←e]; exact F
 intro y; exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
#check giftK
lemma AstroFunding.radius (n m:ℕ)(U': AstroFunding V P_ G S G₀ G₁ X Y Xp q d h Vp Vf T W C BQ Rt Zt b g κp n m): FlagWidth X.p X.K n ∧ SanB X.K (giftK X.p (X.p.supportExponent+(1:ℝ)/2)) X.p h (fun _=> Vf):=by
 obtain ⟨Be,Vκ,Ca,V0⟩:=U'.trust
 obtain ⟨Fv,h1,h2,h3,h4⟩:=V0.heat _ _ _ _ _ (OrbitPulse.nil G X Y h b g U'.anchor U'.hush m l.L)
 obtain ⟨F,R,K0,W'⟩:= h4 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i=>i.elim0)
 rw [←R.age.2] -- only Force residual; be careful when P.Meta rewrite h
 exact ⟨K0 0 roots,R.port 0 roots⟩
end YM.CF.QuadClock
