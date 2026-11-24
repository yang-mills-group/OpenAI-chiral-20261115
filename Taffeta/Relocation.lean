import Taffeta.AdvanceTable
import Taffeta.Navigator
import Sparkle.Circle
import Taffeta.Linen
import Taffeta.Quote
import Sparkle.Curvature
import Sparkle.Seed
import YM.CF.Buffered.StepIdentity
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
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
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Swell Compass Taxi Ione Tune Grain AnalyticBridge.VerifiedReset
open Buffered Larch
namespace Keeping
open Buffered.Advance Mew
variable (A: SiteLedger V U kL q)
local notation "Sc" i:max=>mid (A.side i) B
variable {I:Type}[Fintype I][LinearOrder I]
variable {i0 f v D0:ℕ}{Yz:Vxpert V A}(qZ:PaperTrace V A f v Yz D0)
variable {M: TraceS (mid (A.side i0) B)}
variable (wK wφ:ℝ)(l:Log I (mid (A.side i0) B))(F:Log I (mid (A.side (i0+1)) B))(o:I→Site (mid (A.side i0) B))
variable {hh κ T0:ℝ}
variable (p0:f ≤ i0)(p1:i0<v)
open Buffered.Advance Stencil Buffered.Afterglow.Tower
local notation "mH" r:max=>mid (A.side r) B
variable (Λk Γk:ℕ)(hT: Tickets V D0 Λk Γk R.L A f v)
local notation "pc"=>padding D0 Λk Γk
variable (oK:ℕ)
include hT qZ
-- Step evolution preserving invariant in units of Step. Capture compatibility across external Probe all barriers. 
variable {iJ:ℕ} (oj:I→Site (mid (A.side iJ) B))(rj:I→Mark (mid (A.side iJ) B))(hq:f≤ iJ)(uV:iJ≤v)(hrV:∀ i, AtSupport false (sitepad (oj i) oK) (rj i))(hu:∀ i h:I,i≠h→2*(oK+padding D0 Λk Γk)< separation (node (oj i)) (node (oj h)))
include hq hu hrV
lemma see_adv(s:List I)(p:s.Nodup)(cV:iJ<v) : Yz iJ (couple rj s)=couple (fun i=>Yz iJ (rj i)) s ∧∃ c:ℕ,(∀ i h:I,i≠h→ 2*(c+pc)< separation (node (adapt V A iJ oj i)) (node (adapt V A iJ oj h))) ∧∀ i,AtSupport false (sitepad (adapt V A iJ oj i) c) (Yz iJ (rj i)):=by
 let j:=iJ; let L:= (A.plant j)
 obtain ⟨Z,hs,H,⟨P'⟩,hB,h,r,x⟩:= qZ.clock iJ hq cV
 rw [qZ.choice iJ]; unfold seatLect; rw [←hs]; have hC:=hT.ask iJ hq cV; have hv:1<(A.ratio iJ).count.val:=by rw [hT.side iJ]; have h':=R.coarse; omega
 exact ⟨productFilm V oj oK rj hrV D0 Λk Γk _ (qZ.odd _) (P'.power.symm ▸ H) P' hB hC.1 hu s p, afterBill V oj oK rj hrV D0 Λk Γk _ h (qZ.odd _) hv (P'.power.symm ▸ H) P' hB hC.1 hC.2 hu⟩
include uV
lemma blaze_more (s:List I)(p:s.Nodup): blaze V A Yz iJ v (couple rj s)= (couple (fun j=>blaze V A Yz iJ v (rj j)) s):=by
 suffices t:∀ k:ℕ,∀ (x:ℕ)(_hr:f≤ x)(__:x+k=v)(oj:I→Site (Sc x))(rj:I→Mark (Sc x))(oK:ℕ)(hrV:∀ i,AtSupport false (sitepad (oj i) oK) (rj i))(hu:∀ i h:I, i≠h → 2*(oK+pc)< separation (node (oj i)) (node (oj h))),
    blaze V A Yz x v (couple rj s)=couple (fun i=>blaze V A Yz x v (rj i)) s by exact t (v-iJ) iJ hq (by omega) oj rj oK hrV hu
 intro k; induction k with
 | zero=> intro i u h o r k a b; have h:i=v:=(by omega); subst i; simp only [blaze,hop_here]
 | succ k ih=>
   intro i u h o r m a b; have ht:i<v:=by omega
   have hz(i:ℕ)(X: Mark (Sc i))(h:i<v): blaze V A Yz i v X= blaze V A Yz (i+1) v (Yz i X):=hop_step _ _ _ _ h _ -- inspect
   obtain ⟨g,c,hk,hp⟩:= see_adv V A qZ Λk Γk hT m o r u a b s p ht
   simp_rw [hz i _ ht]; rw [g]; exact ih _ (u.trans (Nat.le_succ _)) (by omega) _ _ c hp hk
omit uV hq hu hrV
lemma markTargetR (i r v:ℕ)(p:i ≤ r)(q:r≤v)(t:I→Site (Sc i))(hp:∀ j k:I,j≠k→2*(oK+pc)< separation (node (t j)) (node (t k))):
  ∀ j k:I,j≠k→ 2*(oK+pc)< separation (node (liftCanvas V A i r t j)) (node (liftCanvas V A i r t k)):=by
 rcases eq_or_lt_of_le p with e|p; · subst r; unfold liftCanvas; rw [hop_here]; exact hp
 unfold liftCanvas; rw [hop_step (h:=p)]
 refine markTargetR (i+1) r v p q (adapt V A i t) ?_ -- section oK fixed. remove
 intro j k g
 have hz(j:I):node (adapt V A i t j)=(ratio (A.ratio i)).embed (node (t j)):=Py.claw (A.ratio i) (qZ.odd _) _
 rw [hz,hz,Laic.emptio]
 exact (hp j k g).trans_le (Nat.le_mul_of_pos_left _ ((ratio (A.ratio i)).count.property))
termination_by r-i
#print axioms markTargetR
#print axioms blaze_more
end Keeping
end Dyad
end YM.CF.Py
end
