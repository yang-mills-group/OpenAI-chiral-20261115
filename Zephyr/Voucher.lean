import Zephyr.Brol
import Zephyr.Basic

/-! `Voucher` expresses matching on every hub of price-depth
(cover count) above a *fixed* cutoff k, to an array bought at raised
rate in full.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Zephyr
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray

open Beau Ione
variable {n:Side}{P:BudgetPoint}{h x y:ℝ}{K L:ℕ}{X Y:RegBudget n}

def Voucher (P:BudgetPoint)(h:ℝ)(K:ℕ)(c:ℝ)(E:RegBudget n):Prop:=
  ∃ T:RegBudget n, IncX Utrue T (plusP P) h c ∧
     (∀ i:Scree.Hub n,K<coverNumber P.B i.val.2 → head_L E i=head_L T i)

namespace Voucher

theorem loan (t:IncX Utrue X (plusP P) h x) : Voucher P h K x X:=⟨_,t,fun i _=>rfl⟩
theorem add (u:Voucher P h K x X)(v:Voucher P h K y Y):Voucher P h K (x+y) (X+Y):= by
  obtain ⟨x',s,r⟩:=u
  obtain ⟨y',p,q⟩:=v
  exact ⟨_,Ione.addT _ s p,fun i t=>by rw [headPlus,headPlus,Pi.add_apply,Pi.add_apply,r i t,q i t]⟩

theorem span (u:Voucher P h K x X)(p:K≤L): Voucher P h L x X:= by
  obtain ⟨x',s,r⟩:=u
  exact ⟨_,s,fun _ t=> r _ (p.trans_lt t)⟩

theorem like (u:Voucher P h K x X)(q:∀ i:Scree.Hub n,K<coverNumber P.B i.val.2 → head_L Y i=head_L X i):Voucher P h K x Y:= by
  obtain ⟨x',s,r⟩:=u
  exact ⟨_,s,fun _ t=> (q _ t).trans (r _ t)⟩

theorem cost (u:Voucher P h K x X)(q:x≤y):Voucher P h K y X:=by
  obtain ⟨T,⟨⟨v,t,f⟩,z⟩,r⟩:=u
  exact ⟨T,⟨⟨v,t,fun i=>(f i).trans q⟩,z⟩,r⟩
end Voucher
end YM.CF.Zephyr
