import GaugeFieldConstruction.Fangs
import YM.CF.Roots.Seat
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
open Flot
set_option maxRecDepth 2800
variable (M:Tulip.Male)
open scoped YM.CF.Mew
variable {T U V:InkD n}{F W:Waves}{a b:ℝ}(h)
-- linear tests (C*)
include M
variable {h}
set_option maxHeartbeats 150000 in
lemma linearHQ (t:MetaB o M F T p h) (u: PressB p X T h a)(s:ℂ)(g:0≤h) : MetaB o M (s • F) (s • T) p h:=by
 let K:ℂ→L[ℝ]ℂ:= s • ContinuousLinearMap.id ℝ ℂ
 let he:= (eraF T _ u g 1 (ping_f p _)).paid
 have hv(i j:tangD n): ploy (s • T) i j= s • ploy T i j:=by rw [ploy_iter,muck T,show s • term T= K ∘ term T from rfl, K.iteratedFDeriv_comp_left (f:=term T) he (i:=2) (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge)),ploy_iter]; rfl
 constructor
 · change (s • (bF4 F).val) = _; rw [t.post]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (hv _ _).symm
 · change s • bF5 F= _; rw [t.mast]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (hv _ _).symm
 · let U:=orbitPH (T 1); let Z:= pawnC s
   rw [Pi.smul_apply, orbit_π M]; -- tune explicit
   have tX: (fun x=>TabX o M h (s • U) x)= fun x=> Z (TabX o M h U x):=by funext x; unfold TabX; rw [stream_c h o M U s x]; simp only [Matrix.smul_mul,Matrix.mul_smul]; rfl
   have hg: postF (chartF F) Z= chartF (s • F):=by
      apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun i=>?_) (dual_uni _ _ fun i=>?_))<;>rfl
   rw [←hg,t.port]; exact ((tab (o:=o) (h:=h) M U|>.geomF Z).equal (Eventually.of_forall fun i=>(congrFun tX i).symm)).unique (tab M _)
 · change s • (bm5 F).val=_; rw [t.mixed]; apply ContinuousLinearMap.ext; intro i;
   let L(t:ℝ):= increment 1 (t • gateC o p.threshold i); let Z:= pawnC s
   have ht: HasDerivAt (fun t=>sectorJ (orbitPH (s • T (L t))) M o h) (s • landA M o T p h i) 0:=by
       simp_rw [orbit_π M -- tune
         ,sector_scale]
       exact Z.hasFDerivAt.comp_hasDerivAt 0 (landR M (o:=o) u i)
   exact ht.unique (landR M (o:=o) (Roots.súe _ _ u s) i)
end Layout
end Lenten
end YM.CF.TableF
end
