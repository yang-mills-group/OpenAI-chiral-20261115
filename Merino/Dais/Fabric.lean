import Merino.Corolla.Curtain
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
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

set_option autoImplicit false
open Mew Waxy Roots Rive Oise

variable {I:Type}[LinearOrder I][Fintype I]
variable {N P B n:Side}
variable {L:Side}
variable (G:Ratio (mid N B) (mid P B))
variable (X:GramM (mid N B))(Y:GramM (mid P B))
variable (o:I→Site (mid N B))
local notation "FINE" => mid P B
local notation "GRAFT" => mid N B
local notation "vFine" => Hove.heel G ∘ o


open Corolla
abbrev laceBoost (B:BudgetPoint):ℝ:= (1+(B.B:ℝ))^100

/-- A zero-core (52) authorization for a tip.
 Even for ANY p* core power enforced on exactly this core box and its smaller choices.
 Includes anchored warranty. -/
structure Exclusive (p:BudgetPoint)(o:Site n)(h w:ℝ)(D:RegBudget n):Prop where
 outer (j:Scree.Hub n): D j≠0 → j.val.1 = node o ∧
      ¬ j.val.2⊆arbour p (node o)
 inner(j:Scree.Hub n)(pstar:BudgetPoint):
   j.val.2⊆arbour p (node o) → PressB pstar j (D j) h 0
 price:∃ v:Scree.Hub n→ℝ,(∀ j,PressB p j (D j) h (v j))∧
   laceBoost p*(∑j,p.mass j.val.2 (v j)) ≤ w

variable {h w:ℝ}{u:ℕ}
lemma isolated (p:BudgetPoint){y:I→Sour.Firing GRAFT}
 {D:Key I→RegBudget GRAFT}{K:Key I→ForceBudget GRAFT}
 (v:Corolla.Fit X o L w u y h D K)
 (t:p=X.p)(s:0≤h) (i:I) (w':ℝ)
 (e:laceBoost p*w ≤ w'):
 Exclusive p (o i) h w' (νTip D i):=by
 subst p
 obtain ⟨g,t,l⟩ :=(v.label i).vest.weight
 let r(j:Scree.Hub GRAFT):ℝ:=if j.val.1≠node (o i) then 0 else g j
 refine ⟨fun j b=>⟨by by_contra c; exact b ((v.label i).site _ c),fun c=> b (v.dry i j c)⟩,fun j p a=>?_,r,?_,?_⟩
 · rw [v.dry i j a]; exact rinse ..
 · intro j; unfold r
   split
   · rename_i y; rw [(v.label i).site _ y]; exact rinse ..
   exact t j
 apply le_trans _ e
 refine mul_le_mul_of_nonneg_left ?_ (by unfold laceBoost; positivity)
 refine Eq.trans_le ?_ (l (node (o i)))
 refine sum_congr rfl ?_
 intro j _
 unfold r
 by_cases h: j.val.1=node (o i)
 · rw [if_neg (not_not.mpr h),if_pos h.symm]
 rw [if_pos h,if_neg (Ne.symm h),BudgetPoint.mass,mul_zero]
