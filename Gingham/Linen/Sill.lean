import Gingham.Linen.Tatting
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Linen
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
open Ione

variable {n:Side}{p:BudgetPoint}{i:Scree.Hub n}{k b:ℕ}
def Sparse (F:RegBudget n) (k b:ℕ):Prop:=
 ∀ i:Scree.Hub n, k<coverNumber b i.val.2→F i=0
lemma Sparse.zaffre {F:RegBudget n} (s:Sparse F k p.B) : Zaffre F p k:=by
 intro i g; funext V; change minusO (F i V)=(0:Cipher n)
 rw [show F i V=0 from congrFun (s i g) V]
 exact minusO_zero
lemma sizeB_move (b:ℕ)(s:Sweep n)(i:Scree.Hub n):
    coverNumber b (moveHub s i).val.2=coverNumber b i.val.2:=glow_q s b i.val.2
lemma Sparse.writ {F:RegBudget n}(t:Sparse F k b):Sparse (writ_E F) k b:=by
 intro i g
 unfold writ_E
 rw [Pi.smul_apply,Finset.sum_apply,sum_eq_zero,smul_zero]
 intro s _
 unfold base_Q; rw [t _ (by rw[sizeB_move]; exact g)]
 funext; exact map_zero (suit_Y _)


lemma Sparse.mono {F:RegBudget n}(t:Sparse F k b)(m:ℕ)(p : k ≤ m):Sparse F m b:=fun i g=>t i (p.trans_lt g)
lemma Sparse.sub {F G:RegBudget n}(t:Sparse F k b)(h:Sparse G k b): Sparse (F-G) k b:=by
 intro i g; rw [Pi.sub_apply,t i g,h i g,sub_zero]
open Larch in
lemma Sparse.sunY {A:Type}{R:Finset A}
   (X:A→Scree.Hub n)(G:A→ InkD n)
   (s:∀ j∈R, k < coverNumber b (X j).val.2 →G j=0)
   [DecidableEq A]:
 Sparse (sunY R X G) k b:=by
 intro i g; apply sum_eq_zero; intro j v; obtain ⟨p,r⟩:=mem_filter.mp v; exact s j p (r.symm ▸ g)

