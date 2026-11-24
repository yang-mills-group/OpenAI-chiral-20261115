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

-- B.P proof dependence evaporates everywhere useful on its present domain.
-- recipes use zealPitch produced AT each v.
local notation "SΩ"=>Seat n
local notation "FCq"=>FC (Dwell n)
local notation "Keyq"=> Key I
local notation "Bep"=> Bag n
variable {M:Key I→ I→ Bag n} {y b:Key I→ I→ Aura n→ℝ}
variable (H:∀ z∈hill I,∀ (i:I)(X:Aura n),Flight P q X h (M z i X) (y z i X) (b z i X))
-- no data off hill
noncomputable def presse (x z:Key I): Rinse (Seat n) (Copy n):= if p:x∈hill I then zealPitch (M x) (y x) (b x) (H x p) z else 0
lemma pressed (x z:Key I)(u:x∈hill I): presse H x z=zealPitch (M x) (y x) (b x) (H x u) z := dif_pos u
lemma presse_form (X Y:Aura n)(D:Support (More n))(W:Copy n)(x z:Key I)(u:x∈hill I)(U:Orbit n) (l:Bias.αt Y X D (cipherK q)): (presse H x z X D Y W U).val= Sault.rind (coll_T P X D ((pinSeries (M x) z) Y) U*(W U).val):=by
 rw [pressed H x z u]; change _=_; exact Bias.truth (v:=l) .. -- args? tactic
lemma press_eq (X Y:Aura n)(D:Support (More n))(t:Key I)(u:Key I)(x z:Key I)(p:t∈hill I)(g:u∈hill I)(v:pinSeries (M t) x Y=pinSeries (M u) z Y): presse H t x X D Y = presse H u z X D Y:=by
 by_cases k:Bias.αt Y X D (cipherK q)
 · funext P' W; apply Subtype.ext; rw [presse_form H X Y D P' t x p W k, presse_form H X Y D P' u z g W k,v]
 rw [pressed H t x p,pressed H u z g]; funext a; unfold zealPitch Bias.payX; rw [dif_neg k,dif_neg k]
variable (p:∀ (X:Aura n)(U:Orbit n),River (fun z:Key I=> pinSeries (M z) z X U))
lemma buoy_mult{β:Type}[NormedRing β][NormedAlgebra ℂ β]{F G: Key I→β}(h:River F)(k:River G):River (fun z=> F z * G z):=⟨h.shore.mul k.shore,fun i v j x y=> (h.slope _ v _ _ y).mul (k.slope _ v _ _ y)⟩
include p
lemma wake_rinse (G:Key I→ Copy n)(X Y:Aura n)(D:Support (More n))(V:Orbit n)(k: River (fun z=> G z V)) : River (fun z:Key I=> presse H z z X D Y (G z) V):=by
 by_cases u:Bias.αt Y X D (cipherK q); swap
 · apply River.cong (zeroR (0:Cipher n)); intro i l; change presse H i i X D Y (G i) V=0; rw [pressed _ _ _ l]; unfold zealPitch Bias.payX; rw [dif_neg u]; rfl
 apply yield_R
 let F(z:Key I):=coll_T P X D ((pinSeries (M z) z) Y) V; have hF:River F:=by unfold F coll_T; split; exact p _ _; exact zeroR _
 let L:=(Pastry.cane (Dwell n)).eval.toContinuousLinearMap; have h:=sc_V (buoy_mult hF (sc_V k sheen)) L
 exact h.cong fun i l=>presse_form H X Y D _ i i l V u -- tune p implicit binder
variable {K:Key I→ForceBudget n}(c: ∀ X:Aura n,∀ D,∀ U: Orbit n,River (fun z:Key I=> settleK (K z) X D U))
local notation "SPX" z:max => presse H z z
local notation "TR" z:max=> settleK (K z)
include c
lemma chip_rinse (X:Aura n)(D:Support (More n))(V:Orbit n)(j:ℕ): River fun z:Key I=> coeff j (Cadre.chip (SPX z) (TR z) X D) V:=by
 induction j using Nat.strong_induction_on generalizing X D with |h j ih=>
    cases j with
    |zero=>simp_rw [Cadre.peg]; exact c _ _ _
    |succ j=>
       have hv(i:Mew.Key I): coeff (j+1) (Cadre.chip (SPX i) (TR i) X D)=((j:ℝ)+1)⁻¹ • coeff j (Cadre.stepL (SPX i) (Cadre.chip (SPX i) (TR i)) X D):=by nth_rw 1 [Cadre.peel]; rw [sprig]
       simp_rw [hv,Pi.smul_apply, Cadre.ore,Finset.sum_apply]; refine bScale _ (tick_sum _ _ (fun i _=> tick_sum _ _ (fun G v=>?_))) _; apply wake_rinse H p; simp_rw [coeff_prod,Finset.sum_apply,Finset.prod_apply]; refine (tip_bank _ _ (fun a y=> cost_R _ _ (fun m w=>?_ ))).1; exact ih (a m) (Nat.lt_succ_of_le (le_trans (single_le_sum (fun i _=>Nat.zero_le (a i)) w) ((mem_finsuppAntidiag.mp y).1.le))) m _
omit c p
lemma chip_hush {σ:I→Seat n} (f:∀ (Y:Aura n), Hush σ Y.val (fun z=>pinSeries (M z) z Y))(g:∀ (Y:Aura n)(D:Support (More n)), Hush σ Y.val (fun z=>settleK (K z) Y D))(i:ℕ)(X:Aura n)(D:Support (More n)):Hush σ X.val (fun z=>PowerSeries.coeff i (Cadre.chip (SPX z) (TR z) X D)):=by
  induction i using Nat.strong_induction_on generalizing X D with
  | h i ih=>
    intro x hx y hy θ
    cases i with
    | zero => simp_rw [Cadre.peg]; exact g X D x hx y hy θ
    | succ i =>
      dsimp only
      nth_rw 1 [Cadre.peel]
      nth_rw 1 [Cadre.peel D ((SPX y))]
      rw [sprig, sprig, Cadre.ore, Cadre.ore]; apply congrArg; refine sum_congr rfl ?_
      intro Y _; refine sum_congr rfl ?_
      intro G l; have hu:X.val=Y.val∪Palot.robe G:= (Cadre.drum_p ..|>.mp l).2.2
      rw [press_eq H X Y D x y x y hx hy (f Y x hx y hy fun i w=> θ i (hu.symm ▸ Finset.mem_union_left _ w))]
      apply congrArg; rw [coeff_prod,coeff_prod]; apply sum_congr rfl; intro k v; apply prod_congr rfl; intro s e
      exact ih _ (Nat.lt_succ_of_le ((single_le_sum (fun j _=> Nat.zero_le _) e).trans_eq (mem_finsuppAntidiag.mp v).1)) _ _ _ hx _ hy fun i w=>θ i (hu.symm ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s,e,w⟩))
end YM.CF.Vow.TreasuryFog
