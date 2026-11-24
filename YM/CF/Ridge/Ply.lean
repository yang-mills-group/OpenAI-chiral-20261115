import YM.CF.Ridge.Quip
import YM.CF.Paxos.Seed
import YM.CF.Chaff.Advent
import YM.CF.Paxos.Heron
import YM.CF.Bloom.Sequence
set_option autoImplicit false

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
open Oath Feu Feu.Corset Beau Haro Ione Salt
set_option maxHeartbeats 1000000
abbrev ply_U(K:Side)(k:ℕ)(s:Sweep N):Prop:=∃ x:Cover,s.b=wrap N ((K^k).val • x)
lemma ply0 (K:Side)(s:Sweep N): ply_U K 0 s:=by refine ⟨lift s.b, ?_⟩; rw [pow_zero]; simp [wrap_lift]
lemma ply_s (G:Ratio N P)(s:Sweep N)(R:Side)(i:ℕ)(v:ply_U R i s)(h:G.count=R):ply_U R (i+1) (reSweep G s):=by
 obtain ⟨x,t⟩:=v; refine ⟨x,?_⟩; change G.embed s.b=_; rw [t,G.embed_wrap,h,pow_succ',show ((R*R^i).val)=(R.val)*(R^i).val from rfl,mul_smul]
lemma ply_J (R:Side)(k':ℕ)(v:Sweep (CSide N (R^k')))(p:ply_U R k' v): Chaff.LabelB N (R^k') v:=by obtain ⟨x,t⟩:=p; refine ⟨ Sweep.mk v.s (wrap (More N) x) v.charge, ?_ ⟩; let B:=R^k'; let L:=Gloss.rBar N B; change Sweep.mk v.s (L.embed (wrap (More N) x)) v.charge=v; rw [Ratio.embed_wrap,show L.count=R^k' from rfl,←t]
end YM.CF.Py
