import YM.CF.BPress.Sea.Pear
/-! caps. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Nougat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Pec Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}(W:Pride N)
variable {P:Pledge} (H:Pledge)
open Sifting
abbrev wRead (H:Pledge) :=Real.exp (18 * H.rate/8)
def tax(H:Pledge):Pledge:= ⟨H.rate/8,32 * wRead H* H.price,div_pos H.pos (by norm_num),mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) H.bought⟩
def layer(W:Pride N) (x:Post N) : Op (Single N):= Matrix.diagonal (fun i:Single N=> Pec.tag (home N i) (W i.1.1) x)
private abbrev w_pay (i j : Single N) (t: Ok N × Ok N) : ℝ:= if i=j then money_i i t W else 0
private abbrev w_layer (i j :Single N)(t:Ok N × Ok N)(x:Post N):= if i=j then stream_i i t W x else 0
variable (i : Single N)
private lemma tariff_f (c:Lac W H.rate H.price): ∑ z:Ok N × Ok N, rent (tax H).rate (footInk i z)*money_i i z W ≤ (tax H).price:=by
 let a:=H.rate/8; have he: 0≤ a:= (tax H).pos.le; refine le_trans ?_ (mul_le_mul_of_nonneg_left (c.pay i.1.1) (by unfold wRead; positivity : 0≤32* wRead H)); unfold cents; rw [Fintype.sum_prod_type]; simp_rw [mul_sum]; apply sum_le_sum; intro z _; apply sum_le_sum; intro j _; let p:= (z,j); let s:= contour (home N i) z j; have hp:rent a (footInk i p) ≤ wRead H * Real.exp (H.rate*s):=by
    unfold rent wRead; rw [←Real.exp_add]; exact Real.exp_monotone ((mul_le_mul_of_nonneg_left (feetInk i p).1 he).trans_eq (by unfold a s p; dsimp only; ring))
 apply (mul_le_mul_of_nonneg_right hp (money_c ..)).trans_eq; unfold money_i s nick Spin.home; dsimp only; ring
lemma cobase (v:Lac W H.rate H.price): (tax H).Costs (Sifting.outlook N).stage (layer W):=by
 have he(i j:Single N)(p:Ok N × Ok N): Expo (Sifting.outlook N).stage (footInk i p) i j (w_pay W i j p) (w_layer W i j p) :=by
    unfold w_pay w_layer; split; next h=> subst j; exact ledger_i i p W
    next h=> exact nothing ..
 refine funds (fun i j k=> he i j k) (fun i=>?_ ) (fun j=>?_ ) (fun x i j=>?_ ) -- not fundRows; column diagonal
 · rw [sum_eq_single i]; simp only [w_pay,if_true]; exact tariff_f W H i v; intro j _ h; simp only [w_pay,Ne.symm h,ite_false,mul_zero,sum_const_zero]; simp
 · rw [sum_eq_single j]; simp only [w_pay,if_true]; exact tariff_f W H j v; intro i _ h; simp only [w_pay,h,ite_false,mul_zero,sum_const_zero]; simp
 by_cases h:i=j; · subst j; simp only [layer,Matrix.diagonal_apply_eq, w_layer,if_true]; rw [Pec.tag,Fintype.sum_prod_type];
 simp only [layer,Matrix.diagonal_apply_ne _ h,w_layer,h,ite_false,sum_const_zero]
end YM.CF.BPress.Nougat
