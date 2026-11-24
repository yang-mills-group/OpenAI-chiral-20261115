import YM.CF.Hove.Yap
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable {ι:Type*}[Fintype ι]
variable (H W:ι→ℝ)(a b l r t u:ι→ℂ)(g k w L B C A D:ℝ)(hp:0 ≤ H)(hQ:0 ≤ W)
lemma windL(V:ι→ℝ)(v:ι→ℂ)(h:0≤V):0≤paidX V v:= sum_nonneg fun _ _=>mul_nonneg (h _) (norm_nonneg _)
def billY(a b l r:ι→ℂ):= dishV a b+dishV a r+dishV l b
local notation "U"=>paidX
include hp hQ
lemma mintK (sL:1≤L)(hB:1≤B)(hD:0≤D)(hL:B≤ 2*L)(hC:0≤C)(hK:0≤k)(ht: U H a≤C*k)(hq:U W b≤ D*k)(hf:U H l ≤ C*(B/L*k))(hg: U W r ≤ D*(B/L*k))(hr:U H (t-(a+l)) ≤ C*(g*k))(hv:U W (u-(b+r))≤D*(g*k))(hl:U W u ≤ w*(D*k))(hZ:0 ≤ g)(h':(B/L)^2≤g): paidX (coilF H W) (dishV t u-billY a b l r) ≤ (w+4)*g*(C*k*(D*k)):=by
 let z:=B/L; let X:= t-(a+l); let Y:= u-(b+r); have h0:0 ≤ coilF H W:=fun i=>mul_nonneg (hp _) (hQ _)
 have he:dishV t u -billY a b l r=dishV X u+dishV (a+l) Y+dishV l r:=by
    unfold billY; have hx:t=X+(a+l):=by unfold X; abel
    have hz:u=Y+(b+r):=by unfold Y; abel
    nth_rw 1 [hx]; rw [dish_l]; nth_rw 2 [hz]; rw [dish_r,dish_l (a:=a) (a':=l)] -- tune
    simp_rw [dish_r,dish_l]; abel
 let P:=C*k; let Q:=D*k; have hy:0≤z:=div_nonneg (zero_le_one.trans hB) (zero_le_one.trans sL); have hB':z≤2:= (div_le_iff₀ (lt_of_lt_of_le zero_lt_one sL)).mpr hL
 have hP:0≤P:=mul_nonneg hC hK; have hQ':0≤Q:=mul_nonneg hD hK
 rw [he]; refine (p_sum (fun i=>h0 i) _ _).trans ((add_le_add (p_sum (fun i=>h0 i) _ _) (le_refl _)).trans ?_); simp_rw [dish_p]
 have hx: U H l ≤ z*P:=hf.trans_eq (mul_left_comm ..); have hy' : U W r ≤ z*Q:=hg.trans_eq (mul_left_comm ..)
 have he₁: U H X ≤ g*P:=hr.trans_eq (mul_left_comm ..); have he₂:U W Y≤g*Q:=hv.trans_eq (mul_left_comm ..); have he₃:U H (a+l) ≤ 3*P:= by refine (p_sum (fun i=>hp i) _ _).trans ((add_le_add ht hx).trans ?_); change P+z*P≤ _; nlinarith
 have hu:0 ≤ w*Q:= (windL W u hQ).trans hl
 refine (add_le_add (add_le_add (mul_le_mul he₁ hl (windL W u hQ) (mul_nonneg hZ hP)) (mul_le_mul he₃ he₂ (windL W Y hQ) (by positivity))) (mul_le_mul hx hy' (windL W _ hQ) (by positivity))).trans ?_
 change _ *(w*Q) + _ + _≤ _*g*(P*Q); rw [show z*P*(z*Q)= z^2*(P*Q) by ring]; exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right h' (mul_nonneg hP hQ'))).trans_eq (by ring)
lemma gold_v (hC:0≤C)(hA:0≤A)(h:U H t≤C*g)(p:U W u≤ A)(hp':U H a ≤ C)(hq:U W b ≤ A)(hL:U H l ≤ C*B)(hR:U W r ≤ A*B): paidX (coilF H W) (dishV t u - billY a b l r)≤ (g+1+2*B)*(C*A):=by
 have hu:0≤coilF H W:=fun x=>mul_nonneg (hp _) (hQ _); let U':=coilF H W; rw [sub_eq_add_neg]; refine (p_sum (fun i=>hu i) _ _).trans ?_; rw [p_negative]; unfold billY
 refine (add_le_add (le_refl _) ((p_sum (fun i=> hu i) _ _).trans (add_le_add (p_sum (fun i=>hu i) _ _) (le_refl _)))).trans ?_; simp_rw [dish_p]; exact (add_le_add (mul_le_mul h p (windL _ _ hQ) ((windL _ _ hp).trans h)) (add_le_add (add_le_add (mul_le_mul hp' hq (windL _ _ hQ) hC) (mul_le_mul hp' hR (windL _ _ hQ) hC)) (mul_le_mul hL hq (windL _ _ hQ) ((windL _ _ hp).trans hL)))).trans_eq (by ring)
end YM.CF.Hove
