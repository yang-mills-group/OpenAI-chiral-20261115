import YM.CF.BProof.Stage.Age
import YM.CF.BProof.Stage.Foam
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N P B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{T:Tube SU.group S}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}{X:GramM (mid N B)}{Y:GramM (mid P B)}
variable {C:Chamber V U W x order power h q e} (D:BasisSt C G T G₀ G₁ X Y a γ w)
namespace BasisSt
local notation "Fo"=> D.Asset
variable {D}
structure Matching(D:BasisSt C G T G₀ G₁ X Y a γ w)(i j:D.Asset)(k:ℝ):Prop where
 common : i.val.βx=j.val.βx
 small : ShiftQ Y.p h (C.δ/2) i.val
 nearB: Books Y.p (j.val.F-i.val.F) h k
 nearK: Pressed Y.p (j.val.K-i.val.K) h k
 pos:0<k
 norm:k≤C.δ/4
variable {i j:D.Asset}{k:ℝ} (m:Matching D i j k)
def limit (ε a:ℝ):= a / (2 * ε)
-- explicit extrapolation only at these allowances
namespace Matching
include m
lemma gt_one:1<limit k C.δ:=by rw [limit,lt_div_iff₀ (by have h:=m.pos; positivity)]; linarith [m.norm,m.pos]
lemma pay_ε:(limit k C.δ-1)⁻¹ ≤ 4*k/C.δ:=by
 have p:=m.pos; have s:=C.ful; rw [inv_le_iff_one_le_mul₀ (sub_pos.mpr m.gt_one)] -- check lemma
 unfold limit; field_simp; nlinarith [m.norm]
def above (z:disk (limit k C.δ)): D.Asset := by
 let v:Parcel (mid P B):= ⟨i.val.βx,i.val.v+(z:ℂ)*(j.val.v-i.val.v),i.val.F+(z:ℂ) • (j.val.F-i.val.F),i.val.K+(z:ℂ) • (j.val.K-i.val.K)⟩
 let hk:= m.small.reg; have hu: C.δ/2 + ‖(z:ℂ)‖ * k ≤ C.δ :=by
    have hx:= (mem_ball_zero_iff.mp z.property); change ‖(z:ℂ)‖ < C.δ /(2*k) at hx; rw [lt_div_iff₀ (by have h:=m.pos; positivity)] at hx; linarith -- grouping linear fails
 let p:= Books.σ m.nearB z.val
 exact ⟨v,i.property.year,⟨Books.mono (Books.plus hk p) hu, Pressed.mono (Pressed.plus m.small.force (Pressed.σ m.nearK z.val)) hu ⟩, ionic_plus i.property.spark (ionic_z (ionic_sub j.property.spark i.property.spark j.property.cost.reg hk C.hP) m.nearB C.hP (z:ℂ)) hk p C.hP⟩
def along (z:ℂ):D.Asset:= if p:z∈ disk (limit k C.δ) then above m ⟨z,p⟩ else i
lemma at_Ω (z:disk (limit k C.δ)):m.along z=m.above z:=dif_pos z.property
lemma at_0:m.along 0=i:=by
 unfold along; rw [dif_pos (d0 m.gt_one)]; apply Subtype.ext; cases he:i.val with | mk βx v F K => dsimp only [above]; rw [he]; simp
lemma at_1:m.along 1=j:=by
 unfold along; rw [dif_pos (d1 m.gt_one)]; apply Subtype.ext; cases he:j.val with | mk βx v F K=> dsimp only [above]; rw [m.common,he]; simp
end Matching
end BasisSt
end Cupboard
end YM.CF.Py
