import GaugeFieldConstruction.ModeH3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Ladder3 Salt Levier Thera Urn Hest Sault Pastry Haro
open XGarden XGarden.MastTin SeasonH Branch Tenant Drapes Rill Nacre Broc SliceRoof
attribute [local instance] boreKSpace boreXN opCStarAlgebra
variable {R:Loom n}{k:ℕ}{t d a c e r h:ℝ} 
variable (F:Elm n Unit d a c)(R:Loom n)(k:ℕ)(t:ℝ)
-- halves option. Cell width one.V orientation motion.
variable (X S D:Support (More n))(W:Orbit n)
local notation "Vx"=> uplift F R k D S t
local notation "Y"=> Single n
local notation "G"=> LeanV (Single n)
-- lore variants.Import Meas axis
variable (u:Roof n t d k R)(q:0<d){P:BudgetPoint}{K T:ℝ}(p0:Hann P k t)(tK:hud_T 7 K)(hp:coinH K T)(ht:0≤T)
include u q
section
local notation "Ψu"=> XGarden.MastTin.SeasonH.Hitz -- tune
local notation "Ω"=> χH F R k t
-- cost.$δ_. via call budgets.
def pint3 (S:Support (More n)):ℝ:= if S.card=1 then 1 else 0
private lemma spint:0≤ pint3 S:=ite_nonneg zero_le_one le_rfl
abbrev BillLeg (S:Support (More n))(d v a c:ℝ)(F:Elm n Unit d a c):= pint3 S+BudgetValve v d*ζΧ d a c F S
include ht
lemma Vegan3:0≤BillLeg S d T a c F:=add_nonneg (spint R k t S u q) (mul_nonneg (by unfold BudgetValve DeskK composeCost; positivity) (Hook_p ..)) -- tune
omit ht
lemma σΔ (i:G) :Measurable (fun z=> iceK (χH F R k t S z D) i):=by
 let V:=fun z:Orbit n=> χH F R k t S z D; have he:= lift_meter (F:=F) (S:=S) (D:=D) u q
 have p(a b:G): Measurable (fun z:Orbit n=>V z a b):=by
    letI : MeasurableSpace (Op (Single n)):=borel _; haveI:BorelSpace (Op (Single n)):=⟨rfl⟩
    have hm(i j:Y):Measurable (fun z:Orbit n=>uplift F R k D S t z i j):= ((show Continuous (fun R:Op (Single n)=> R i j) from (continuous_apply j).comp (continuous_apply i)).measurable).comp he
    rcases a with ⟨a,i⟩; rcases b with ⟨b,j⟩; cases a <;>cases b; exact measurable_const; exact measurable_const.sub (hm i j); exact measurable_const.add (hm j i); exact measurable_const
 unfold iceK; apply Finset.measurable_fun_sum; intro j _; exact (p i j).smul_const _ -- tune
variable (vh: 1 ≤ h)(hx: Lattice.halo (k+22) S⊆ X)(hy:Lattice.halo (cipherK k) D⊆ X)
include h vh hx hy tK hp ht p0
local notation "cΩ"=> BillLeg S d T a c F
lemma κ_Duty (i j:Y)(V:Lime P X D): Pence P.order (fun s=> uplift F R k D S t (citrus P X D V s) i j) 0 (BudgetValve T d* Wloop F S i j):=by
 let B:=citrus P X D V; let G0:=cram (F:=F) u q tK ht hp p0 h vh S X D hx hy i j V; let YM:=bare_p _ _ G0
 refine YM.mono (le_of_eq ?_); rw[p0.canon]; unfold BudgetValve; norm_num; ring -- tune
lemma Υμ (i:G): Portμ (citrus P X D) (0:tangD n) (fun z=>iceK (χH F R k t S z D) i) h (h⁻¹ * BillLeg S d T a c F) P.order:=by
 let Z:= BudgetValve T d; have hZ: 0≤ Z:=by unfold Z BudgetValve DeskK composeCost; positivity
 have h':=zero_lt_one.trans_le vh
 let B(i j:Y):= ‖sip0 S i j‖ + Z * Wloop F S i j
 have hv(i j:Y):0≤ B i j:=add_nonneg (norm_nonneg _) (mul_nonneg hZ (loop_p ..)) -- tune unused Bh
 let gW:= Wloop F S; let P0(v:Bool)(i j:Y):=if v then B j i else B i j
 have hμ(v:Bool)(i j:Y)(m:Lime P X D):Pence P.order (fun s=> χH F R k t S (citrus P X D m s) D (v,i) (!v,j)) 0 (P0 v i j):=by
    have hp(i j:Y):=κ_Duty F R k t X S D u q p0 tK hp ht vh hx hy i j m -- tune shadow locals/order
    cases v; swap; · exact Pence.add (Pence.const ..) (hp j i)
    let C:= fun z:tangD n=> uplift F R k D S t (citrus _ _ _ m z) i j
    have h₀: Pence P.order (-C) 0 (Z*gW i j):=by
       simpa only [norm_neg,norm_one,one_mul,neg_smul,one_smul] using (show Pence _ ((-1:ℂ) • C) 0 (‖(-1:ℂ)‖*(Z*gW i j)) from Hake.Pence.σ _ (hp i j))
    exact Pence.add (Pence.const ..) h₀
 have hBill(i:Y): (∑ j:Y,B i j)≤ cΩ ∧(∑ j:Y,B j i)≤ cΩ:=by
    have hR(i): (∑ j:Y, ‖sip0 S i j‖) ≤ pint3 S ∧ (∑ j:Y, ‖sip0 S j i‖)≤ pint3 S:=by -- diagonal
       constructor <;> (rw [sum_eq_single i]; rotate_left 1; · intro j _ p; rw[sip_e,if_neg (fun q=>?_ ),norm_zero]; first| exact p q.2 | exact p q.2.symm)
       · simp
       · rw [sip_e]; split
         next p=> rw[pint3,p.1,card_singleton]; norm_num
         rw[norm_zero]; exact spint R k t S u q
       · simp
       · rw [sip_e]; split
         next p=> rw[pint3,p.1,card_singleton]; norm_num
         rw[norm_zero]; exact spint R k t S u q
    unfold B; rw[sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum]; unfold BillLeg ζΧ
    refine ⟨add_le_add (hR i).1 (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun i=> ∑ j:Y,Wloop F S i j) ?_ (mem_univ i)) hZ),?_ ⟩
    · intro j _; exact sum_nonneg fun _ _=>loop_p ..
    apply add_le_add (hR i).2 (mul_le_mul_of_nonneg_left (b:= ∑ j:Y, Wloop F S j i) ?_ hZ)
    refine sum_le_sum fun j _=>single_le_sum (f:=fun i=>Wloop F S j i) (fun i _=>loop_p ..) (mem_univ i)
 rcases i with ⟨b,i⟩; let L(j:Y)(z:Orbit n):= χH F R k t S z D (b,i) (!b,j) • takeF (n:= Dwell n) (!b,j)
 have qL: (fun z=> iceK (χH F R k t S z D) (b,i))=∑ j:Y,L j:=by
    funext z; unfold iceK; rw [Fintype.sum_prod_type,sum_eq_single (!b)]
    · exact (Finset.sum_apply z _ L).symm -- tune
    · intro j _ v; cases b<;>cases j <;> (first| contradiction| exact sum_eq_zero fun _ _=> zero_smul _ _)
    simp
 have hp0(j): Portμ (citrus P X D) 0 (L j) h (P0 b i j * h⁻¹) P.order := (mist_t P.order _ h (0:tangD n) (!b,j) h').scale _ (by unfold P0; split <;> exact hv _ _) (hμ b i j)
 rw [qL]; refine (Portμ.sum _ _ _ (fun j _=>hp0 j)).rise ?_ h'.le; rw [←sum_mul,mul_comm]; refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr h').le; cases b; exact (hBill i).1; exact (hBill i).2
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
