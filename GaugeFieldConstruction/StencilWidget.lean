import YM.SU5.SatinWard.Resolution.Spirea
import GaugeFieldConstruction.Metope
set_option autoImplicit false
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
open Tap Waxy Ione.Clock StressFlux SU
namespace SignSlot
open Buffered Swell Porticus Hest Nacre StressExchange Merino.Brooch
local notation "K0"=> Op SU.Slot
open Advance Buffered.Afterglow.Tower Tilted
open Lampshade
-- single travel proofs around W calls, retain Ramp exact at gauge/clover and arm directions.
variable (s:Sweep N)(Z:Tilted.Ramp)(i:Axis)(z:ℤ)
-- Symmetry pays a geometric vignette spanning the two conventions for rotation here. Load first on `C.affirms` costs.
local notation "B^" B:max=> (⟨B,0⟩:Shape)
open YM.CF.Buffered YM.CF.Buffered.Jubilee YM.CF.Buffered.Lifted
lemma wakeAxisSt(B:Signed)(u v:Cover)(h:B.act (nodeC u)= nodeC v)(n:Side):Earlier (Levier.ray (N:=n) false (B^ B)) (wrap n v) (wrap n u):=by
 unfold Earlier; rw [sitA,Levier.ray,(assembly n).embed_wrap]; rw [node_of,node_of]; exact (Shape.anno (B^ B) (N:=n) (nodeC u)).trans (congrArg (wrap _) (show (B^ B).motion (nodeC u)=nodeC v from by simpa [Shape.motion] using h))
open CF.Sour
lemma spinRecited_st (n:Side)(A:Signed) (y x:Cover)(p:A.act (nodeC x)=nodeC y)(z:ℝ)(f:Op SU.Slot)(h:star f=f) (u:Mark n)
      (hu:u= z • onsiteSensor (wrap n y) (petal (A.perm i) ⊗ₖ f)) : SweepTurn n (Levier.ray false (B^ A)) u ((↑(StressFlux.sign A i):ℂ) • z • onsiteSensor (wrap n x) (petal i ⊗ₖ f)):=by
 let s' := Levier.ray (N:=n) false (B^ A); let W:=onsiteSensor (wrap n x) (petal i ⊗ₖ f); let Z:= (StressFlux.sign A i); let Y:= z • W
 have he : ((↑Z:ℂ) • Y)=flyMark s' u:=by
    rw[hu,fly_scale]; change _= z • flyMark s' (onsiteSensor _ (petal (s'.s.perm i) ⊗ₖ f)); rw [spin_shift s' i f h _ _ (wakeAxisSt A x y p n) rfl]; change (↑Z:ℂ) • z • _=z • Z • _; rw [smul_comm z, Complex.coe_smul]
 rw [he]; exact ⟨fliesTransport s' u⟩
#print axioms spinRecited_st
end SignSlot
end YM.CF.QuadClock
end
