import GaugeFieldConstruction.BraveryN
import GaugeFieldConstruction.CannesN
import GaugeFieldConstruction.CassioCurrencyVU
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
open BrentFe
open YM.GaugeFieldConstruction Flavor -- potential namespace collision
open BluffV BluffV.Fables
local notation "χK"=>↥CompassN
open Afterglow Satin Tapestry Six
lemma braveryCurrencyVU (x:Cover)(i:Matter.FlavorIndex)(K:Buffered.Calibration) : BraveryN x i K ≤ CurrencyVU K:=by
 refine Submodule.span_le.mpr ?_; rintro f ⟨a,h,p,c,r,e⟩; obtain ⟨g,T,B,u,v,z,k⟩:= pocketingN (K:=K) a c r (fun q=>by subst a; exact h) p (fun _ q=> cart_M q (by omega))
 rw [e,←z]; exact paysCurrencyVU T B u k
#print axioms braveryCurrencyVU
end YM.CF.XGarden.MastTin.ArtCart
end
