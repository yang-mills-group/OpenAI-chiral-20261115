import YM.CF.Vp929.Pre.Ambit
import Zephyr.Cast
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
variable (p:0<d)(vx:0≤a)(h':1≤h)
open Wray
-- sweep obligations. elementary linear algebra lemmas.
open Lilt
namespace Cash
open Zephyr
variable {F G:Pax n}(τ:Ids n)(pL:MonoQ P h (prominence P) F w)(pA: poise F)
local notation "dF"=> due τ F
local notation "fQ"=> Cash.returnV τ P F
include h' pL
include pA
lemma priceRPlus : IncX Utrue (Cash.earn τ P F) (plusP P) h (reserveT P.power P.order P.B 1*(w+w)) ∧ Packed P h (prominence P) (Cash.owe τ F) w:=by
 obtain ⟨S,T,V⟩:= charter h' τ pL; have hc(X:Aura n):Vow.Medal P X.val ∅ (cashV dF X) h (S X):= (Medal.oneT.rum (dF X)).big (by rw [mul_one]; exact T X)
 have hg(x:Aura n):0 ≤ S x:=(norm_nonneg _).trans (T x); refine ⟨?_ ,S,⟨hg,fun i D v l=>Larch.nom_F h' P i _ (hc i) D ⟩,V⟩
 let H:MonoQ P h (prominence P) (F-cashV dF) (w+w):= pL.sub ⟨S,hc,V⟩; obtain ⟨L,b,q⟩:=H; exact worthRplus P fQ τ (booths τ pA).2 (booths τ pA).1 (zero_le_one.trans h') (fun i=>zen_B P (b i)) q
#print axioms priceRPlus
end Cash
end YM.CF.Py.Rate
