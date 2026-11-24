import Zephyr.Brol
import Zephyr.Dawn
import YM.CF.Vp929.Canon.Knit
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
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
open AnalyticBridge.VerifiedReset.Collection
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d v α σ C Λ β j w:ℝ}
local notation "D'"=> RegBudget n
local notation "V'"=> Skye.Seat n
local notation "Gξ"=> SU.group
local notation "Px"=> Lattice.PlaqAxes
local notation "φ"=> AnalyticBridge.VerifiedReset.petals
local notation "H_"=> AnalyticBridge.VerifiedReset.heads
local notation "Z_"=> AnalyticBridge.VerifiedReset.counter
local notation "Lρ"=> Cash.prominence Q
variable {R:PathData SU.group}{b:Clip}(u:Cease Q R b α v σ C Λ n) (T:Ids n) (g:1 ≤ h)
local notation "Fr"=> c
local notation "Θ_"=> ΘK T Q R b (-1)
local notation "ℓ1"=> (lite_b n Q R b (-1))
local notation "ℓ2"=> (lit_P n Q R b (-1))
local notation "μr"=> (rate_b Q b σ C α (-1))
local notation "μp"=> (rate_h Q b σ C α (-1))
local notation "Λr"=> (rate_μ Q b σ C v (-1))
local notation "Kp"=> Push.BetaTransport.kinetic
namespace QuiltB
variable {F:Scree.Hub n→ Scree.Hub n}(p:Extension L Q n F)
local notation "CR"=> creditR Q R b n
local notation "CT"=> creditT Q R b T

include g u T
lemma mutePack : Silent (packR Q R b F):=
  light_F _ (scalar_warp ((creditTune u T g).2.2.1))
end QuiltB

namespace TestW


variable {F:Scree.Hub n→ Scree.Hub n}
lemma cappedShave (Y:RegBudget n)(i:Scree.Hub n) (hi:1 < coverNumber Q.B i.val.2) :
    shaveL Q Y i = 0:= by
  have hp:i∉massH Q:=fun m=>hi.not_ge (mem_filter.mp m).2
  exact if_neg hp
lemma cappedNet (p:Extension L Q n F) (Y:RegBudget n)(i:Scree.Hub n)
    (hi:max 1 (mstar L) < coverNumber Q.B i.val.2) :
    NetX F Q Y i=0:=by
  change shaveL Q Y i - writ_E (warp_E F (shaveL Q Y)) i=0
  rw [cappedShave Y i (lt_of_le_of_lt (le_max_left _ _) hi)]
  have hU : writ_E (warp_E F (shaveL Q Y)) i=0:=by
    apply writStops (max 1 (mstar L)) Q.B _ i hi
    intro j h
    refine sum_eq_zero (fun l v=> cappedShave Y l ?_)
    rw [←(mem_filter.mp v).2] at h
    by_cases s:shortHub Q L l
    · rw [p.cap l s] at h
      exact False.elim (h.not_ge (le_max_right ..))
    rw [p.held l s] at h
    exact (le_max_left _ _).trans_lt h
  exact sub_eq_zero.mpr hU.symm

open QuiltB
include g u T
lemma cappedAlign {L:Side}(p:Extension L.val Q n F) (q:↥SpaceM)(η:↥SpaceM→ₗ[ℝ] RegBudget n)
    (i:Scree.Hub n)(d:ℝ) (hi:max 1 (mstar L.val)<coverNumber Q.B i.val.2) :
    head_L (aligner Q L F q (QuiltB.packR Q R b F) η d) i=0:=by
 unfold aligner
 rw [headPlus,headScale,mutePack u T g,smul_zero,add_zero]
 funext V
 change cut_V (NetX F Q (η q) i V)=0
 rw [cappedNet p _ i hi, Pi.zero_apply,map_zero]
#print axioms cappedAlign
end TestW
end Test
end YM.CF.Py.Rate
