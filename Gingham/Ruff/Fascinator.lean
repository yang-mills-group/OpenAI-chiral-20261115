import SatinThinGarage
import SatinThinPlant
set_option autoImplicit false
set_option maxHeartbeats 1090000
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

namespace Preparation

/-- Extra loans selected before appointment for kernel charges in §§XXI.
    funde at j=4 rather than Teller K.j to preserve independence. -/
structure Fascinator (V: Grace K R L) (e:ℝ) where
 a : ℝ
 cost : ℝ
 m : ℕ
 pos : 0<a
 hi : 0<cost
 one : ∀ (N:Side), m ≤ N.val → ∀ M:Male, Tulip.Solo a cost (funde 4 M N) e
 two : ∀ (N:Side), m ≤ N.val → ∀ Q:Aim N, Q.toll V.f V.g V.F1 V.F2 →
        Tulip.Solo a cost (Moire.bloom Q) e

abbrev Fascinated (P: Preparation) := Nonempty (Fascinator P.V P.d)

-- need link via Arc i
lemma secure_pin : ∃ d> (0:ℝ), ∀ e> (0:ℝ),e≤d → Nonempty (Fascinator V e) := by
 let A:=arcB V.f V.g V.F1 V.F2
 let B : WG (QuotaH V.f V.g V.F1 V.F2):= fun i=> funde 4 i.2
 have g:Lively A := (Cour.alum V.pos1.le V.pos2.le V.width1 V.width2).1
 have h:Lively B:=by
   obtain ⟨x,f,a,i,r,s,t,v⟩:= funde_s 4 (by decide)
   exact ⟨x,f,a,i,r,s,t,fun j=> v j.2⟩
 obtain ⟨x,r,d,i,z,p,t,aa,bb⟩:= g.link h
 refine ⟨d,p,fun e w hw=>⟨x,r,t,i,z,?_,?_⟩⟩

 · intro N p M
   let Z:QuotaH V.f V.g V.F1 V.F2 := ⟨fun n=>⟨_,Cour.xx0 n V.pos1.le V.pos2.le⟩,M⟩
   exact Tulip.axis_down _ _ (bb Z N p) _ w hw
 intro N p' Q g'
 let M : Male := ⟨R.L,R.odd_side⟩
 obtain ⟨z,hz,_⟩:= Cour.demand N V.pos1.le V.pos2.le Q g' M
 rw [← hz]
 exact Tulip.axis_down _ _ (aa z N p') _ w hw

end Preparation
