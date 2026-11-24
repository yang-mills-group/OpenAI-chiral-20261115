import Anomaly.Hop.Wipe
import Anomaly.Compass.Fathom
import Anomaly.Compass.Lute
import YM.CF.Roots.Patch
import YM.CF.Brood.Veep
/-! Matrix Key operations on all issued inventories. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew
variable {n N B:Side} {I:Type} [LinearOrder I] [Fintype I]
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots Py Oise Swell Sault Pastry Rue
local notation "Tc"=> mid N B
local notation "Hp"=> hill I
-- linear readout same row λ. supports any algebra over values on Slots
variable {D A:Type*}[DecidableEq D]
def markerCore {A:Type*}[AddCommMonoid A][SMul ℂ A](σ:I→D)(M:I→I→ℂ)(X:I→ A) (i:I):A:=∑ j∈pipe_ζ σ i,M j i • X j
variable (σ:I→D)(M:I→I→ℂ) [AddCommMonoid A][Module ℂ A] (X:I→ A)
local notation "Vζ"=> toV_C σ M
lemma marker_tax (z:Key I): ∑ i:I,z i • markerCore σ M X i = ∑ i:I,toV_C σ M z i • X i:=by
 let F(i j:I):= z i • M j i • X j
 have hv(i:I): z i • markerCore σ M X i= ∑ j:I,if σ j=σ i then F i j else 0:=by rw [←sum_filter,markerCore,Finset.smul_sum]
 have h(j:I) :Vζ z j • X j= ∑ i:I,if σ j=σ i then F i j else 0:=by
    rw [←sum_filter,toV_C,sum_smul]; refine sum_congr ?_ fun i _=>?_ ; swap; · unfold F; rw [smul_smul,mul_comm]
    ext i; simp only [pipe_ζ,mem_filter,eq_comm]
 simp_rw [h,hv]; rw [sum_comm]
lemma moves_α (Z:I→ℂ): α_ξ (markerCore σ M Z) = (α_ξ Z) ∘ toV_C σ M:=funext fun z=> marker_tax σ M Z z
omit [AddCommMonoid A] [Module ℂ A]
lemma movesΖ : Vζ 0=0:= funext fun _=>sum_eq_zero fun _ _=>mul_zero _
-- suppress at dead Keys of entire root. matrix with closed pipes.
lemma moves_pin (i j:I)(x:ℂ) : toV_C σ M (update 0 i x) j=if σ j=σ i then M j i*x else 0:=by
 split
 next h=> unfold toV_C; rw [sum_eq_single_of_mem i (mem_filter.mpr ⟨mem_univ _,h.symm⟩), update_self]; intro b _ v; rw [update_of_ne v]; exact mul_zero _
 next h=> apply Finset.sum_eq_zero; intro k p; rw [update_of_ne (fun b:k=i=> h (((mem_filter.mp p).2 |> (congrArg _ b).symm.trans).symm))]; exact mul_zero _
lemma pine_c (T:Finset I)(z:1<T.card)(p:Set.InjOn σ T)(i:I)(v:ℂ): Mew.pine T (toV_C σ M (update 0 i v))=0:=by
 obtain ⟨x,w,y,t,k⟩:= one_lt_card.mp z
 by_cases h:σ x=σ i; · exact prod_eq_zero t (by rw [moves_pin,if_neg (fun v:σ y=σ i=> k (p w t (h.trans v.symm)))])
 exact prod_eq_zero w (by rw [moves_pin, if_neg h])
end YM.CF.Vow.TreasuryFog
