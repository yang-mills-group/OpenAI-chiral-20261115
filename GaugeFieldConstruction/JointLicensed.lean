import GaugeFieldConstruction.Dockets
import GaugeFieldConstruction.JointEntrance
import PF.Fountain

/-!
# Joint pre-election funding for the two field franchises. Adapted from GaugeFieldConstruction/Tutelage, Dockets and LocalFieldBounds PF/Fountain.
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
variable {F' G' Q₀ C:ℝ→ℝ}{F:(s:Side)→Scree.Loom s→Prop}{N0:ℕ}{W:GivenX V U}{M:Side}{J:Robes M V W}(q:Chi)(b:ℕ)(h a τ :ℝ)(F0:Scrolls B)
namespace LocalLimit
open Preparation
theorem jointLicensing {Q:Badge}(p: Marketable Q)(X:TintDemand)(TintRq: TintDemand)(NLeaf Tleaf:ℕ): CommissionVector (fun P=> LicensedHeight Q NLeaf X P ∧ (TintRateCommercial Tleaf TintRq P ∧ (Solstitial P ∧ Fountain P)) ∧ Meritorious P ∧ 8∣P.M.val):=by
     constructor; intro a b pH G; obtain ⟨P, l, Z, Y, u,e,t,h,g,attic,⟨w,⟨ξ,z,c⟩,pref,T⟩,u₀,p₀,v,V,x⟩:= (jointLatchSt p X TintRq NLeaf Tleaf).purchased a b pH G
     exact ⟨P,l,Z,Y,u,e,t,h,g,attic,⟨w,⟨ξ,z,⟨c.flow⟩⟩,pref,T⟩,u₀,p₀,v,V,x⟩
#print axioms jointLicensing
end LocalLimit
end Rate
end YM.CF.Py
end
