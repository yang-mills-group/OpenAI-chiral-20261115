import YM.CF.Salt.Flax
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(X:Stores S)(r k:ℕ)
open Acorn Plume Atala Eire
local notation "H"=> Hos S r
local notation "Ζ"=> laden S f r
local notation "Θ"=> reSweep G f
local notation "Λ"=> luckP G S f r
local notation "L"=> liftK S
variable (Y:Finset (Kite S r))(A:Ids (mid P B))
local notation "W"=> (mid P B)
variable (U V:Pane (mid P B))(Bv:Finset (Hos S r))
variable {D:Side}{j k' κ:ℕ}{o:Odd D.val}{P₀:Pricing j D o (Thread j)}{e:ℝ}{P':Grasp P₀ B e}{Q:Aim (mid P B)}{J:Pride (mid P B)}{M:Male}{α τ v a c b m w y:ℝ}
variable (C:∀ Y: Support (Domain P B), Lend P B e Y)(Q':Tints P B e)(B₁:Dyes τ e J k' Q' v m)(B₂:Hive.Vista P' M Q C k' α y w a)
variable (U₀ U₁ V₀ V₁:Pane (mid P B))
variable (pV: Paths S r U₀ U Y)(tV:Paths S r V₀ V Y)(tU:Paths S r (flashA (reSweep G f) U₀) U₁ (Y.image (luckP G S f r)))(gU: Paths S r (flashA (reSweep G f) V₀) V₁ (Y.image (luckP G S f r)))(h₀:HullK S k Y U V e)(h₁:HullK S k (Y.image (luckP G S f r)) U₁ V₁ e)(hA:Injective (priorP A))
variable (q:Seat (mid P B)→SU.E)(F:List (Hos S r))(B': Ride S)(l:ℕ)
variable (hq:Paths S r (Lattice.gauge q U₀) U₁ Y)(hg:Paths S r (Lattice.gauge q V₀) V₁ Y)(hk:HullK S k Y U₁ V₁ e)
lemma perma(P :∀ i∈Y,∀ K,K⊆L Y→postM S k C Q' U V A K i=postM S k C Q' U₁ V₁ A K i) : Eire.paint S k C Q' U V A Y F= Eire.paint S k C Q' U₁ V₁ A Y F:=by
 induction F with
 | nil=>rw [Eire.paint, Eire.paint]
 | cons i z ih=>
    rw [Eire.paint,Eire.paint, ih]; refine congrArg₂ (·*·) ?_ rfl; unfold Eire.rankG; split; exact sum_congr rfl fun j v=> P _ (mem_filter.mp v).1 _ inter_subset_left; rfl
-- arbitrary stalke.M same.
open MeasureTheory CF.Appel CF.Summit Next Push.SectorMeasure -- tune
variable {ι:Type}[Fintype ι][DecidableEq ι]{Xv:ι→ Palot.leaf (Site (Domain N B))}{Xf:GramM (mid P B)}{Mk:Forge.Monk SU.group S}
lemma guardF (F G':Eire.Dress G S e r l Mk Xf k Xv)(Y:Troupe S r ι)(X:Ride S)(x:ℝ)(z:ℕ)(t:CrownB G S e (F.coats Y) (G'.coats Y) k X)(a:F.portT=G'.portT)(b:F.portG=G'.portG)(hs:F.songP Y=G'.songP Y)(hF:F.brew Y=G'.brew Y)(hp:F.bodyL x z Y=G'.bodyL x z Y): vigor (F.stageT x z Y) X=vigor (G'.stageT x z Y) X:=by
 let A:=F.stageT x z Y; let B:=G'.stageT x z Y; have hz(j: Ride S)(v:j≤X):vig A j=vig B j:=by
    apply Subtype.ext; change Scion.tempo A j=Scion.tempo B j; unfold Scion.tempo; by_cases h: Scion.cluster (BranchX S Xv k) Y≤ j; swap; · rw [if_neg h,if_neg h]
    rw [if_pos h,if_pos h]; change issue (F.heatT Y j) (F.bodyL _ _ _).val (F.songP Y)*(F.brew Y).val=issue (G'.heatT Y j) (G'.bodyL _ _ _).val (G'.songP Y)*(G'.brew Y).val
    rw [←hp,←hs,←hF]; refine congrArg₂ (·*·) ?_ rfl; unfold Eire.Dress.heatT; rw [←a,←b]; exact Plume.ca_l F.portT F.portG F.guardP _ _ _ t v _ _ _ (A.capP j h) (A.forP j h)
 apply Stilo.proves; intro j p; exact (Scion.recon (vig A) j).trans ((hz j p).trans (Scion.recon (vig B) j).symm)
end YM.CF.Salt
