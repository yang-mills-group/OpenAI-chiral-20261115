import YM.CF.Rive.Silk
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
lemma tariffP (G: Mew.Key ι→ Copy n)(t:River (fun i=>G i V))(Y:Aura n): River (fun i=> c.payX X D Y (G i) V):=by
 by_cases v:Bias.αt Y X D δ; swap
 · apply River.cong (zeroR (0:Cipher n)); intro i _; change c.payX _ _ _ _ V=0; unfold Bias.payX; split; contradiction; rfl
 apply yield_R; let A:= ((ContinuousLinearMap.mul ℂ (FC (Dwell n))) (coll_T P X D (H Y) V)); let L:= (Pastry.cane (Dwell n)).eval.toContinuousLinearMap; exact (sc_V (sc_V (sc_V t sheen) A) L).cong (fun i p=>c.truth X D Y (G i) v V)
lemma cost_R {K':Type*}[NormedCommRing K'][NormedAlgebra ℂ K'][CompleteSpace K']{J:Type*}(I:Finset J)(P:J→Key ι → K')(p:∀ i∈I,River (P i)):River (fun j=> ∏ i∈I,P i j):=by
 classical
 induction I using Finset.induction_on with
 | empty=>simpa using (zeroR (I:=ι) (1:K')) -- tune
 | insert i I h t=>simp_rw [prod_insert h]; exact River.mul_T (p _ (mem_insert_self ..)) (t (fun j hj=>p _ (mem_insert_of_mem hj)))
lemma bScale(p:Key ι→ Cipher n)(h:River p)(k:ℝ): River (fun i=> k • p i):= (h.scale (↑k:ℂ)).cong (fun i _=>rfl)
variable (Fv:Mew.Key ι→Cusp n)(Ft:∀ U:Aura n,∀ D,∀ V,River (fun z=>Fv z U D V))
local notation "M" i:max=> chip c.payX (Fv i)
include c Ft
lemma arm_R (j:ℕ) : River fun i:Mew.Key ι=> coeff j (Cadre.chip c.payX (Fv i) X D) V:=by
 induction j using Nat.strong_induction_on generalizing X D with |h j ih=>
    cases j with
    |zero=>simp_rw [Cadre.peg]; exact Ft _ _ _
    |succ j=>
       have hv(i:Mew.Key ι): coeff (j+1) (Cadre.chip c.payX (Fv i) X D)=((j:ℝ)+1)⁻¹ • coeff j (Cadre.stepL c.payX (Cadre.chip c.payX (Fv i)) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [hv,Pi.smul_apply, Cadre.ore,Finset.sum_apply]; refine bScale _ (tick_sum _ _ (fun i _=> tick_sum _ _ (fun G v=>?_))) _; apply tariffP z V c X D; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; refine (tip_bank _ _ (fun a y=> cost_R _ _ (fun m w=>?_ ))).1; exact ih (a m) (Nat.lt_succ_of_le (le_trans (single_le_sum (fun i _=>Nat.zero_le (a i)) w) ((mem_finsuppAntidiag.mp y).1.le))) m _ -- tune
lemma arm_F (j:ℕ): River fun i:Mew.Key ι=> coeff j (Cadre.nutL c.payX (Fv i) X D) V:=by
 cases j; · simp_rw [show ∀ s,(coeff 0 (Cadre.nutL c.payX (Fv s) X D)) V=(0:Cipher n) from fun _=> by rw [tick_r]; rfl]; exact zeroR _
 rename_i j; unfold nutL; simp_rw [sprig,Pi.smul_apply,Cadre.front,Cadre.rill,map_sum,grate, coeff_mk,Finset.sum_apply]; refine bScale _ (tick_sum _ _ (fun i _=> tick_sum _ _ (fun G v=>?_))) _; apply tariffP z V c X D; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; exact (tip_bank _ _ (fun a y=> cost_R _ _ (fun m w=>arm_R z V c m _ Fv Ft _ ))).1
variable (l:3 ≤ P.B)(w_:1 ≤ h)(r':Key ι→ Aura n→ Support (More n)→ℝ)(hK:∀ i∈hill ι,∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (Fv i X D) (r' i X D))
variable (S L t μ w s γ a Hb:ℝ)(b: Palot.leaf (Seat n)→ℝ) (Tt:∀ i∈hill ι,Timer (Cadre.chip (cribR z) (r' i)) z S L μ b s γ a Hb w 2 z)(ht:0<t)(hv:t ≤ L-μ*2)
local notation "dp"=> (2*(Hb*γ+s*t⁻¹*γ*a))
include w_ c Tt l hK ht hv
lemma lantern_M(u:D⊆X.val):River fun i=> lamp (P:=P) (Fv i) c.payX X D V:=by
 have hp:= zero_le_one.trans w_; have hh:River (fun i=> rem_X (P:=P) (Fv i) c.payX X D V):=by
    unfold rem_X lasting zenS; split; swap; exact zeroR _
    next hx=>
      let g:= loom_v 0 0 b 2 X; let k:= dp; let A:=k/g
      obtain ⟨Y,hp',hx'⟩:=hx; refine bill_t _ (fun j=> arm_F z V c X D Fv Ft j) ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)).mul_left A) fun i h j=>?_
      let Mm:= nutL (cribR z) (r' i); have a:= deck (Fv i) (r' i) (hK i h) _ z (c.buys l hp) hp X D u j; have hu:= a.merit.same V (Y,V.2) hx' (fun _ _=>rfl); change ‖coeff j (nutL c.payX (Fv i) X D) V‖ ≤ _; rw [hu]; apply le_trans (a.merit.capF w_ (Y,V.2) hp'); apply Cadre.palm_ Mm _ S (Tt i h).slope 0 0 b k _ X D u j
      · exact fun o R p=>Cadre.heatR z (r' i) (fun Y D t=> ((hK i h Y D t).merit.wage hp)) ((c.buys l hp).dice) _ _
      exact fun z m=>(Tt i h).worth ht le_rfl (le_trans (zero_add t).le hv) _ (fun _ _ _=>tick_r _ _) (oreL0 _ _) z m -- he
 exact dub_V (dub_V (Ft X D V) (zeroR _)) hh
end YM.CF.Rive
