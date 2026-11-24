import Anomaly.Ship.Lease
import Anomaly.Ship.Pod
import Anomaly.Ship.TwinZ
import Anomaly.Apert.Lift
import Anomaly.Apert.Price
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots
-- earned Root-v keyed regulator rep. Analytic both fresh and old together.
-- expose First pins on separated Θ tests
variable {N B:Side}
local notation "Fᴷ" => mid N B
set_option maxHeartbeats 700000
local notation "F₀"=> Orbit (mid N B)
open Py Oise Swell Sault Pastry Rue
variable {R:GramM (mid N B)}{L:Side}{wL:Odd L.val}{i_:ℕ}{X: Pricing i_ L wL (Thread i_)}{e':ℝ}(U:Grasp X B e')(C:Scree.Loom (mid N B))
variable {D:Finset I}{σ:I→ Site (mid N B)}{E:Key I→ RegBudget (mid N B)}{K:Key I→ForceBudget (mid N B)}{r:Key I→ℂ} -- uses notation K inside variable sec: hidden N? Lean emits. check
lemma F_pos {s t v:ℝ}(p:Furnace R D q σ E K r h s t v) (u:1 ≤ h):0≤ s∧ 0≤ v:=by
 obtain ⟨Z,V,b,Q,x,y⟩:=p.buds
 obtain ⟨M,e,t⟩:= Q.wage; obtain ⟨C,f,g⟩:=t _ roots
 obtain ⟨H,V',x⟩:= (p.San 0 roots).bit
 refine ⟨e ▸mul_nonneg (zero_le_one.trans (reserve_lever ..)) (le_trans ?_ (g 0)),le_trans ?_ (x 0)⟩
 · exact sum_nonneg fun i _=>mul_nonneg ((f i).wage (zero_le_one.trans u)) (Real.exp_pos _).le
 apply sum_nonneg; intro i _; apply mul_nonneg _ (gradeQ _ _ (V' i) (zero_le_one.trans u)); unfold giftK; split; exact (Real.exp_pos _).le; exact le_rfl
lemma pocketPlus(c:Occlus R.p)(p:0 < c.κ):0≤ yσE R.p c∧0≤ yσF R.p c:=by
 have hv:= c.hγ; have hd:= c.hη; have he:= c.degree0; unfold yσE yσF; unfold reserveT coin_n stilK
 constructor; · refine mul_nonneg (by positivity) (mul_nonneg hv.le (inv_nonneg.mpr (sub_nonneg.mpr he.le)))
 positivity
end YM.CF.Vow.TreasuryFog
