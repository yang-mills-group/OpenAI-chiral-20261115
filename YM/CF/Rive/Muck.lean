import YM.CF.Rive.Grid
import YM.CF.Mew.Bill
import YM.CF.Pso.Loft
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rive
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Mew Sour Stax
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable {P:BudgetPoint}{h:ℝ}{δ:ℕ}(z:Aura n→ℝ)
open PowerSeries
open Salt Ione Levier
variable {H:Bag n}(V:Orbit n)(c:Bias δ H P h z)
-- parameter continuity on tagged input via μ.H.Bitmap
attribute [local instance] loreM loreN -- variables hk earlier.PC
variable {ι:Type}[Fintype ι][LinearOrder ι](X:Aura n)(D: Support (More n))
lemma hush_Y (p:D⊆ X.val)(Y:Aura n)(F:Finset (Aura n))(h:F∈ Cadre.drum X Y D):∀ i∈F,i.val⊆ X.val:=fun i t k v=> by
 rw [((Cadre.drum_p ..).mp h).2.2]; exact mem_union_right _ (show _∈ Palot.robe F from mem_biUnion.mpr ⟨_,t,v⟩)
variable (G:Mew.Key ι→ Cusp n)(σ:ι→Seat n)(hc:∀ (X: Aura n) D,Hush σ X.val (fun z=> G z X D))
include c hc
lemma arm_X (i:ℕ)(p:D⊆ X.val): Hush σ X.val (fun z=> coeff i (Cadre.chip c.payX (G z) X D)):=by
 induction i using Nat.strong_induction_on generalizing D X with |h i ih=> cases i with
    |zero=> simp_rw [peg]; exact hc _ _
    |succ k=>
       have hv(i:Mew.Key ι): coeff (k+1) (Cadre.chip c.payX (G i) X D)=((k:ℝ)+1)⁻¹ • coeff k (Cadre.stepL c.payX (Cadre.chip c.payX (G i)) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [hv,Cadre.ore]
       intro x hx y hy hq; apply congrArg; apply sum_congr rfl; intro Y u; refine sum_congr rfl (fun F v=>?_); apply congrArg; simp_rw [coeff_prod]; refine sum_congr rfl ?_; intro i g; refine prod_congr rfl fun j l=> ih ((i _) ) ((single_le_sum (fun h _=>Nat.zero_le (i h)) l).trans_lt ((mem_finsuppAntidiag.mp g).1.trans_lt (Nat.lt_add_one _))) j _ inter_subset_right _ hx _ hy fun k v_=> hq k (hush_Y X D p Y F v j l v_)
lemma arm_B (p:D⊆X.val): Hush σ X.val (fun v=> lamp (P:=P) (G v) c.payX X D):=by
 intro x hx y hy hp; change _+ _ = _ + _; apply congrArg₂ (·+·); exact congrArg₂ (·+·) (hc _ _ _ hx _ hy hp) rfl
 funext v; unfold rem_X lasting zenS; split; swap; rfl
 refine tsum_congr fun i=> ?_; apply congrFun (f:=coeff i (Cadre.nutL _ (G x) X D)); change coeff i _=coeff i (nutL c.payX (G y) X D); cases i; · rw [show coeff 0 _=_ from tick_r ..,show coeff 0 (nutL c.payX (G y) X D)=_ from tick_r ..] -- pattern
 rename_i i; unfold nutL; rw [sprig,sprig]; apply congrArg;  unfold Cadre.front; rw [map_sum,map_sum]; simp_rw [rils]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro F t; apply congrArg; simp_rw [coeff_prod]; exact sum_congr rfl fun a _=>prod_congr rfl fun m w=> arm_X z c _ _ G σ hc (a m) inter_subset_right _ hx _ hy (fun k v'=> hp k (hush_Y X D p j F (mem_inter.mp t).1 m w v')) -- order
end YM.CF.Rive
#print axioms YM.CF.Rive.arm_X
