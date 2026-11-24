import Taffeta.BothRanges
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
open ThinGauge
variable (C D:ℕ→ℝ)(L0:Side){i j s r0 u0:ℕ}
abbrev gainCost(L0:Side):ℝ:= Bmain/(Xη L0)^4
lemma gainCost_pos :0 < gainCost L0:= by unfold gainCost; exact div_pos bm_pos (by unfold Xη; positivity)
lemma hC64 : gainCost L0 ≤ ThinGauge.boost (Xη L0)/64 :=by
 unfold gainCost ThinGauge.boost ThinGauge.gain; have h:0<Xη L0:=by unfold Xη; positivity
 have hq:0<(Xη L0)^4:=by positivity
 field_simp; nlinarith [Real.exp_pos (-1)]
lemma gainBoundS{iT:ℕ}(v:iT ≤ r0)(p:∀ j:ℕ,iT≤ j → j< r0→ Niche L0 (C j) 0):|hGain C r0 iT| ≤ gainCost L0^(r0-iT):=by
 rcases eq_or_lt_of_le v with e|v; · rw [e,gain_here, Nat.sub_self,pow_zero, abs_one]
 rw [show r0-iT=r0-(iT+1)+1 from by omega,pow_succ',gain_step C iT r0 v,abs_mul]; exact mul_le_mul (p iT le_rfl v).amp (gainBoundS (iT:=iT+1) (Nat.succ_le_of_lt v) (fun j h u=>p j (Nat.le_trans (Nat.le_succ _) h) u)) (abs_nonneg _) (gainCost_pos L0).le
termination_by r0-iT
local notation "sR"=> ThinGauge.boost (Xη L0)
lemma sub_quote(t:i < r0)(p:∀ j:ℕ,i≤ j → j< r0→ Niche L0 (C j) (D j)):
    |D i * hGain C r0 (i+1)/(sR^(r0-(i+1)))|≤ (1/8:ℝ) * (64:ℝ)⁻¹ ^ (r0-(i+1)):=by
 have hg:=gainBoundS C L0 (iT:=i+1) (r0:=r0) t (fun j h v=>let e:=p j ((Nat.le_succ i).trans h) v; ⟨e.non,e.amp,(by rw [abs_zero]; norm_num),e.back⟩)
 let k:=r0-(i+1); have hp:sR>0:=boostP L0
 rw [abs_div,abs_mul,abs_of_pos (pow_pos hp _), div_le_iff₀ (pow_pos hp _)]
 have hz:=mul_le_mul (p i le_rfl t).tax hg (abs_nonneg _) (by norm_num)
 change |D i| * _≤ (1/8:ℝ)* (64:ℝ)⁻¹ ^ k * sR^k
 refine hz.trans ?_
 rw [mul_assoc,←mul_pow]
 gcongr
 simpa [div_eq_mul_inv,mul_comm] using hC64 L0
lemma revenue_vac {iT:ℕ}(e:iT≤j)(u:j≤ r0)(p:∀ y:ℕ,iT≤ y→y< r0→Niche L0 (C y) (D y)):
    |revenue L0 C D r0 iT - revenue L0 C D r0 j| ≤ (1/4:ℝ)*(64:ℝ)⁻¹^(r0-j) - (1/4:ℝ)*(64:ℝ)⁻¹^(r0-iT):=by
 rcases eq_or_lt_of_le e with e|v; · rw [e,sub_self,sub_self,abs_zero]
 have hp:=revenue_vac (iT:=iT+1) v u (fun y h z=>p y ((Nat.le_succ _).trans h) z)
 have hl:iT< r0:= v.trans_le u
 let w:=D iT*hGain C r0 (iT+1)/(sR^(r0-(iT+1)))
 let y(k:ℕ):= revenue L0 C D r0 k
 have he:y iT = y (iT+1)+w:= by unfold y; rw [revenue,if_pos hl]
 have ht:|w| ≤ (1/8:ℝ)*(64:ℝ)⁻¹^(r0-(iT+1)):=sub_quote C D L0 hl p
 change |y iT- y j| ≤_
 rw [show y iT-y j=(y (iT+1)- y j)+w from (by rw [he]; ring),show r0-iT=r0-(iT+1)+1 from (by omega),pow_succ]
 refine (abs_add_le ..).trans ((add_le_add hp ht).trans ?_)
 let x:ℝ:= (64:ℝ)⁻¹^(r0-(iT+1)); have hx:x≥0:=by unfold x; positivity
 change (1/4:ℝ)* _-(1/4:ℝ)*x+(1/8:ℝ)*x ≤ (1/4:ℝ)*_ -(1/4:ℝ)*(x*64⁻¹)
 linarith only [hx]
termination_by j-iT
lemma fare_toll(v:i≤ r0)(p:∀ j:ℕ,i≤ j → j< r0→ Niche L0 (C j) (D j)):|revenue L0 C D r0 i - 1| ≤ (1:ℝ)/4:=by
 have h:=revenue_vac C D L0 v le_rfl p; rw [show revenue L0 C D r0 r0=1 from ?_,Nat.sub_self,pow_zero,mul_one] at h; exact h.trans (sub_le_self _ (by positivity))
 rw [revenue,if_neg (lt_irrefl _)]
#print axioms fare_toll
end Keeping
end Dyad
end YM.CF.Py
end
