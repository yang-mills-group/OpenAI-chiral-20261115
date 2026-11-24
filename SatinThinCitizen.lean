import SatinThinChronicle
import SatinThinDelivery
import YM.CF.DPress.Motto.Shade

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

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


open Kay.WagesC.Blend StressFlux AnalyticBridge.VerifiedReset Buffered Buffered.Advance
-- generic scalar over any Pane-height n (avoid insisting n.mid)
variable {n:Side} (x:Site n)(a t:ℝ)
abbrev starBand:= Lattice.halo 12 {node x}
lemma stormB : Lattice.halo 2 {node x}⊆ starBand x:= Corona.halo_mono (by norm_num) (Subset.refl _)
lemma anchor_band : Lattice.halo 2 (Φrap n x 10).val.2⊆ starBand x:=by
 intro i z; obtain ⟨j,h,t⟩:=halo_spec.mp z; obtain ⟨k,h',u⟩:=halo_spec.mp (show j∈Lattice.halo 10 {node x} from h); exact halo_spec.mpr ⟨k,h',(separation_triangle k j i).trans (by omega)⟩
lemma coinZlocal: LocalOn (starBand x) (clothMark a t x):=by
 intro U V b; unfold clothMark quadScore; rw [(ping_location _ (agrees_mono b (anchor_band x)))]; split; swap; exact rfl
 simp_rw [show ∀ j:PlaqAxes, petals U (node x) j= petals V (node x) j from fun j=> petals_reads _ j _ _ (agrees_mono b (stormB x))]
lemma token_local_m (x:Skye.Seat n) : Continuous (quadScore x):=by unfold quadScore; fun_prop
-- needs K instance real? 
lemma coinZenv:Envelope (clothMark a t x):=by
 rw [show clothMark a t x= Set.indicator {U|(pingS t (Φrap n x 10).val.2 U)} (fun U=> a/t^2*quadScore (node x) U) from rfl]
 exact Buffered.env_indicator _ (ping_o.measurableSet) (Girt.refill (fun U=> a/t^2 * quadScore (node x) U) (continuous_const.mul (token_local_m _)) id measurable_id) -- tune
/-- Initial rank-sensitive budget. Use only first links, pupil at actual node. -/
noncomputable abbrev turfMark(a t:ℝ)(x:Site n)(W:Fields n) : FC (Single n):= (↑(clothMark a t x W.1):ℂ) • 1
lemma cup_owns : AtSupport false (starBand x) (turfMark a t x):= by
 refine ⟨Env.along (g:=Prod.fst) (F:= (fun v:Pane n=> (↑(clothMark a t x v):ℂ) • (1:FC (Single n)))) ?_ measurable_fst,fun _ _ u _=> congrArg (fun v:ℝ=> (↑v:ℂ) • (1:FC (Single n))) (coinZlocal x a t _ _ u),fun _=> Reed.Fine.one.scale _⟩
 exact Girt.pole_w (clothMark a t x) (fun v:ℝ=> (↑v:ℂ) • (1:FC (Single n))) (by fun_prop) (coinZenv ..)
lemma cup_gauge (k: Site (More n)→SU.group.El)(U:Pane n) : clothMark a t x (Lattice.gauge k U)=clothMark a t x U:=by unfold clothMark quadScore; simp_rw [petals_gauge,SU.group.norm_adjoint,pingB] -- tune
#print axioms cup_owns
end YM.CF.QuadClock
