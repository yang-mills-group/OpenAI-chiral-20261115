import YM.CF.Stax.Horizon
import YM.CF.Pith.Pole
import YM.CF.Stax.Cast
import YM.CF.Sour.Park
import YM.CF.Sour.Tile
import YM.CF.Ione.Tape
import YM.CF.Cadre.Point
import YM.CF.Cadre.Gear
import YM.CF.Vow.Grow
import YM.CF.Bake.Pep
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
variable {P h δ}
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
open Salt Ione Levier Sour
variable (s:Sweep n)
local notation "Ta"=> Salt.actY s
local notation "Tu"=> moldA s
local notation "Pu"=> Palot.robe
local notation "SD"=> Support (More n)
local notation "Πt"=> (boxA s).symm.toEmbedding
local notation "σX'"=> σX (n:=n) P
variable {H:Bag n}(V:Orbit n)(c:Bias δ H P h z)(p:Injective (priorP V.2)) -- tune shadow
variable (hb:∀ i:Orbit n,Injective (priorP i.2)→∀ X:Aura n,H (moldA s X) (yellA s i)=sauce s.charge (detX s.s) (Sour.γS s) (H X i))
local notation "M"=> Cadre.chip (Bias.payX c) F
local notation "M'"=> nutL (Bias.payX c) F
local notation "Λ"=> Ione.suit_Y s
local notation "W'"=> yellA s V
variable (e:∀ X:Aura n,∀ D⊆X.val,F (moldA s X) (actY s D) (yellA s V)= Ione.suit_Y s (F X D V))
variable {m:ℕ}
-- parameter continuity on tagged input via μ.H.Bitmap
variable {ι:Type}[TopologicalSpace ι][Nonempty ι](H0:ι→Bag n)(C:∀ i:ι,Bias δ (H0 i) P h z)(hk:∀ (X:Aura n)(V:Orbit n),Continuous (fun i=> H0 i X V))
attribute [local instance] loreM loreN -- variables hk earlier.PC
local notation "Δ"=> Support (More n)
abbrev νp (H0:ι→Bag n)(C:∀ i,Bias δ (H0 i) P h z)(i:ι): Rinse (Seat n) (Copy n):=(C i).payX
local notation "Ψ" i:max=> (νp z H0 C i)
variable (X:Aura n)(D: Support (More n))
include hk
lemma turnV (F:ι→ Copy n)(t:Continuous (fun i:ι=> F i V))(Y:Aura n): Continuous (fun i:ι=> (Ψ i) X D Y (F i) V):=by
 by_cases u:Bias.αt Y X D δ; swap
 · have he(i): (Ψ i) X D Y (F i) V=0:=by unfold νp Bias.payX; rw [dif_neg u]; rfl
   simp_rw [he]; exact continuous_const
 rw [continuous_induced_rng]; change Continuous (fun i=> ((Ψ i) X D Y (F i) V).val); simp_rw [show ∀ i:ι,((Ψ i) X D Y (F i) V).val=_ from fun i=>(C i).truth X D Y (F i) u V]; apply ( (Pastry.cane (Dwell n)).eval.continuous_of_finiteDimensional).comp; exact (show Continuous (fun i=>coll_T P X D (H0 i Y) V) from (by unfold coll_T; split; exact hk _ _; exact continuous_const)).mul (continuous_subtype_val.comp t)
lemma rod_k (j:ℕ) : Continuous fun i:ι=> coeff j (Cadre.chip (Ψ i) F X D) V:=by
 induction j using Nat.strong_induction_on generalizing X D with |h j ih=>
    cases j with
    |zero=>simp_rw [Cadre.peg]; exact continuous_const
    |succ j=>
       have hv(i:ι): coeff (j+1) (Cadre.chip (Ψ i) F X D)=((j:ℝ)+1)⁻¹ • coeff j (Cadre.stepL (Ψ i) (Cadre.chip (Ψ i) F) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [hv,Pi.smul_apply, Cadre.ore,Finset.sum_apply]; refine Continuous.smul (f:=fun (_:ι)=>((j:ℝ)+1)⁻¹) continuous_const ?_; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro G v; apply turnV z V H0 C hk X D; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; refine continuous_finsetSum _ fun a y=> continuous_finsetProd _ fun m w=>?_ ; exact ih (a m) (Nat.lt_succ_of_le (le_trans (single_le_sum (fun i _=>Nat.zero_le (a i)) w) ((mem_finsuppAntidiag.mp y).1.le))) m _ -- tune order
lemma rod_e (j:ℕ):Continuous fun i:ι=> coeff j (Cadre.nutL (Ψ i) F X D) V:=by
 cases j; · simp_rw [show ∀ s,(coeff 0 (Cadre.nutL (Ψ s) F X D)) V=(0:Cipher n) from fun _=> by rw [tick_r]; rfl]; exact continuous_const
 rename_i j; unfold nutL; simp_rw [sprig,Pi.smul_apply,Cadre.front,Cadre.rill,map_sum,grate, coeff_mk,Finset.sum_apply]; refine Continuous.smul (f:=fun (_:ι)=>((j:ℝ)+1)⁻¹) continuous_const ?_; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro G v; apply turnV z V H0 C hk X D; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; exact continuous_finsetSum _ fun y _=> continuous_finsetProd _ fun m q=>rod_k F z V H0 C hk m _ _
variable (l:3 ≤ P.B)(w_:1 ≤ h)
include hF l w_
lemma rise_C (u:D⊆X.val)(p:Aqua (Nd X D)):Continuous fun i=> rem_X (P:=P) F (Ψ i) X D V:=by
 unfold rem_X Vow.lasting zenS; split_ifs with v; swap; exact continuous_const
 obtain ⟨Y,x,t⟩:=v; refine continuous_tsum (fun j=> rod_e F z V H0 C hk X D j) p.of_norm fun j i=>?_ ; have hp:= (deck F r hF _ z ((C i).buys l (zero_le_one.trans w_)) (zero_le_one.trans w_) _ _ u j).merit; let Q':=Y; change ‖coeff j (nutL (C i).payX F X D) V‖ ≤ _; rw [hp.same V (Y,V.2) t (fun _ _=>rfl)]; exact hp.capF w_ _ x
lemma light_e (u:D ⊆ X.val)(p:Aqua (Nd X D)):Continuous fun i=> lamp (P:=P) F (Ψ i) X D V:=by
 unfold lamp; simp_rw [Pi.add_apply]; refine (continuous_const.add ?_).add (rise_C F r hF z V H0 C hk X D l w_ u p); unfold birthL; split_ifs; exact turnV _ _ _ _ hk _ _ (fun _=> (1:Copy n)) continuous_const _; exact continuous_const
end YM.CF.Stax
