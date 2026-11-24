import YM.CF.Vp929.Canon.Knit
import Gingham.Linen.Sill
import Gingham.Linen.Crepe
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
namespace TestW
open Fir
open SU Bloch Tap
variable {n L:Side} {M:Male} {j:ℕ} {q C d a b v A t:ℝ}
variable {F:RegBudget n}{P:BudgetPoint}{s:Finset (Scree.Hub n)} (vS:liveB s)
local notation "E0"=> Op (Single n)
local notation "E2"=> SpinIdx × SU.Slot
local notation "WW" u:max=> heroP u
local notation "Ψ"=> StackL F s
local notation "μX"=> (1:Pane n)
local notation "ρX"=> spar j M (1:Pane n)
open Salt Vow Bake Larch Cycle929
local notation "Hz"=> Scree.Hub n
local notation "k_"=> L.val


open Linen
/-- uniform k sufficient for hood -/
def span_cover (L:ℕ) := max 1 (mstar L)
lemma shave_sparse (F:RegBudget n): Sparse (rightS P F) 1 P.B:=by
 intro i g
 rw[rightS,if_neg]
 exact fun q=>not_le.mpr g (mem_filter.mp q).2
variable (ℓ:ℕ)(T:Scree.Hub n→Scree.Hub n)(pe: Extension ℓ P n T)
include pe
lemma warp_sparse {F:RegBudget n} (u:Sparse F 1 P.B): Sparse (warp_E T F) (span_cover ℓ) P.B:=by
 apply Sparse.sunY
 intro j _ h
 by_cases h₁ : shortHub P ℓ j
 · have v:=pe.cap j h₁
   rw [v] at h
   exact False.elim (not_lt.mpr (le_max_right ..) h)
 rw [pe.held j h₁] at h
 exact u j ((le_max_left ..).trans_lt h)

lemma netX_sparse (F:RegBudget n): Sparse (NetX T P F) (span_cover ℓ) P.B:=
 let g:=shave_sparse (P:=P) F
 (g.mono _ (le_max_left ..)).sub ((warp_sparse ℓ T pe g).writ)


variable {α σ C Λ:ℝ}{R:PathData SU.group}{b_:Clip} (u:Cease P R b_ α v σ C Λ n)
open QuiltB
include u
lemma align_frost (g:↥SpaceM)(η:SpaceM→ₗ[ℝ] RegBudget n)(y:ℝ):
 Zaffre (aligner P L T g (packR P R b_ T) η y) P (span_cover ℓ):=by
 let h:Silent (packR P R b_ T):= light_F _ (scalar_warp (creditTune u (Classical.arbitrary _) (le_refl 1)).2.2.1)
 intro i a
 change frosting ((NetX T P (η g))+y • packR P R b_ T) i=0
 rw [Zaffre.sweet (Sparse.zaffre (netX_sparse ℓ T pe _)) _ a]
 ext1 v
 rw [show frosting (y • packR P R b_ T) i v=minusO (y • _) from rfl,frost_cut,map_smul,sass h,smul_zero]
 rfl
#print axioms align_frost

