import YM.CF.Vp929.Pre.Livery
import YM.CF.Vp929.Pre.Ambit
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Bake Gas Wray Larch Nor
variable {a s d δ γ:ℝ}{G H:Pax n}

namespace Cash
open Lilt
variable {T:Set ℂ}(openH:IsOpen T)(τ:Ids n) (i:Aura n)
variable {F:ℂ→ Pair (Pax n)}(e:Census T F)(P:BudgetPoint)
include openH e
lemma on_due : Form T (fun z=> (due τ (F z).1 i,due τ (F z).2 i)) := by
 unfold due Mat_R; simp_rw [Pi.smul_apply, Finset.sum_apply]
 let f(a:Sweep n)(z:ℂ):Pair ℝ:= (zeal_F a (fun j=>vault_Z ((F z).1 j (1,τ))) i,zeal_F a (fun j=>vault_Z ((F z).2 j (1,τ))) i)
 have hF(a:Sweep n): Form T (f a):= ((e (moldA a i) (1,τ)).form openH).probe (Complex.reCLM.comp ((chipV ∅).restrictScalars ℝ))
 exact (form_ballot univ T f fun i _=> hF i).probe (plight_C n • ContinuousLinearMap.id ℝ ℝ)
lemma on_return : Census T fun z=>(returnV τ P (F z).1,returnV τ P (F z).2):=by
 intro i v; unfold returnV zenS; by_cases u: visible P i.val ∅ v.1
 · simp_rw [if_pos u]
   let A:=on_due openH τ i e; let B:= ContinuousLinearMap.toSpanSingleton ℝ (1 : Cipher n); exact (((e i v).form openH).sub (A.probe B)).holo openH
 simp_rw [if_neg u]; exact (form_const T (0 : Pair (Cipher n))).holo openH
lemma on_claim : Census T fun z=>(earn τ P (F z).1, earn τ P (F z).2):= by
 intro i V; let t:= bassH (lagE i) • ContinuousLinearMap.id ℝ (Cipher n); exact (((on_return openH τ e P (lagE i) (V,τ)).form openH).probe t).holo openH
lemma on_lit : Query (fun _=> Set.univ) T fun z=>(owe τ (F z).1, owe τ (F z).2):= by
 intro i _ _ v; let H:= on_due openH τ i e; let L:= -ContinuousLinearMap.toSpanSingleton ℝ (1:Cipher n); exact (H.probe L).holo openH
end Cash
end YM.CF.Py.Rate
