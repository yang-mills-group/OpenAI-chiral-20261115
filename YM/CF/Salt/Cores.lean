import YM.CF.Salt.Bore
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
variable {ι:Type}[Fintype ι][DecidableEq ι]{Xv:ι→ Palot.leaf (Site (Domain N B))}{Xf:GramM (mid P B)}{Mk:Forge.Monk SU.group S}
lemma face_v (F G':Eire.Dress G S e r l Mk Xf k Xv)(Y:Troupe S r ι)(x:ℝ)(z:ℕ)(p:F.pipe=G'.pipe)(q:F.chi=G'.chi)(u:F.wage=G'.wage)(t:F.cloth=G'.cloth):F.bodyL x z Y=G'.bodyL x z Y:=by unfold Eire.Dress.bodyL; rw [t,u,p,q]
end YM.CF.Salt
