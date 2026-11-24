import GaugeFieldConstruction.Lumb
/-! # On cover Foot pricing; coarse height weights.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {c f: Side}(G:Ratio c f)(p:Odd G.count.val)(A: Site f)(M:Male)(T:Script Male)(e:Use 4 G.count T)
variable {d n:ℕ}
abbrev Ladder(x:Cover):ℝ:=1+lateral x
abbrev wagN(n:ℕ)(x:Mill):ℝ:= Ladder x.1^n
lemma ladE (i:Cover):1≤Ladder i:=le_add_of_nonneg_right (Nat.cast_nonneg _)
lemma wagE (i:Mill)(n:ℕ):1≤ wagN n i:= one_le_pow₀ (ladE _)
lemma wl0 (i:Mill):wagN 0 i=1:=by unfold wagN; rw [pow_zero]
lemma wl_up (x y: Cover):Ladder (x+y) ≤ Ladder x* Ladder y:=by unfold Ladder; apply (add_le_add_right (show (lateral (x+y):ℝ)≤lateral x+lateral y by exact_mod_cast lateral_add ..) _).trans; nlinarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (lateral x)) (Nat.cast_nonneg (α:=ℝ) (lateral y))]
variable {G M}
def Honed (R:Side)(M:Male)(u:Bool)(U σ:ℝ):Prop:=∀ (r:Site R)(a b: SpinIdx)(D:List Axis),D.length≤3→ Width σ (U*wool R D) (Hed u 4 R M.val r a b D)
def αN (L:Side):= (L.val:ℝ)⁻¹
abbrev budT (R:Side)(x:ℝ):=wool R [] * x
lemma α_pos(L:Side): 0 < αN L:=inv_pos.mpr (by exact_mod_cast L.property)
lemma αsmall(L:Side):αN L ≤1 :=inv_le_one_of_one_le₀ (by exact_mod_cast L.property)
lemma BudT_v (L:Side){x:ℝ}(v:0<x):0<budT L x:=by unfold budT wool; exact mul_pos (mul_pos (zero_lt_one.trans_le (HarmP.span_one _)) (div_pos (Real.sqrt_pos.mpr (side_pos _)) (by positivity))) v
lemma wool_is (R:Side)(u:List Axis):wool R u=wool R []*αN R^u.length:=by unfold wool αN; rw [pow_add,inv_pow]; simp; ring
local notation "Λ"=> G.count
variable (G)
def usingF (x:Cover):ℝ:=1+ αN Λ*lateral x
lemma using_v (x:Cover):1≤ usingF G x:= le_add_of_nonneg_right (mul_nonneg (α_pos _).le (Nat.cast_nonneg _))
lemma loft_H (x:Cover): Ladder (loft G A x)≤ 9*usingF G x:=by
 let H:=Λ; let Z:= dockLoc G A x; let v:=αN Λ
 have hp:(lateral (loft G A x):ℝ)≤4+v*lateral Z:= Trellis.scost Z
 let L:=lateral x; have hx:(lateral Z:ℝ) ≤ L + 4*H.val:=by
    unfold Z dockLoc; let ht:= (lateral_add x (lift (PatchLoc G A))).trans (add_le_add_right (lift_moon (PatchLoc G A)) L); -- tune Int left issues
    exact_mod_cast ht
 have hv:v*↑H.val=1:=inv_mul_cancel₀ (by exact_mod_cast H.property.ne')
 unfold Ladder usingF; apply le_trans (b:=1+(4+v*(↑L+4*H.val))) (add_le_add_right (hp.trans (add_le_add_right (mul_le_mul_of_nonneg_left hx (α_pos _).le) _)) _)
 rw [mul_add,mul_left_comm v 4,hv]; change (1:ℝ)+ (4+(v*L+4*1))≤ 9*(1+v*L); linarith only [show 0≤ v*L from mul_nonneg (α_pos _).le (by positivity)]
abbrev BudgetX(G:Ratio c f)(σ U:ℝ)(n:ℕ) := (Fintype.card Kt:ℝ) *widthCost σ n*(9:ℝ)^n*(budT G.count U)
lemma Bux_pos (G:Ratio c f)(U σ:ℝ)(v:0<U)(h:0<σ)(k:ℕ):0 <BudgetX G σ U k:=by unfold BudgetX; have ht:=widthCost_ge h k; have hv:=BudT_v G.count v; positivity
variable {G A}
private lemma huY (u:Cover→ℂ)(n:ℕ)(σ C:ℝ)(v:Width σ C u)(h:0<σ): chime (fun x=> Ladder x^n) u (widthCost σ n*C):=by
 let q:= widthCost σ n; let r(x:Cover):=Real.exp (σ*lateral x)*‖u x‖; have hv:SumBudget r C:=v
 apply SBqual (SBscale hv (t:=q) (zero_le_one.trans (widthCost_ge h n))) (by unfold Ladder; intros; positivity); intro i; unfold r q
 refine (mul_le_mul_of_nonneg_right (widthBill σ h n (lateral i) (by positivity)) (norm_nonneg _)).trans_eq (by ring)
variable {t V s:ℝ}{u:Bool}
lemma gene_budget {G:Ratio c f}{A:Site f}(h:Honed G.count M u V s)(p:0 < V)(l:0 < s) (X:Cover)(Y: Kt)(D:List Axis)(v:D.length ≤3)(n:ℕ) : chime (wagN n) (ware G A M u D X Y) ((BudgetX G s V n)*αN G.count^D.length*(usingF G X)^n) :=by
 let f:=ware G A M u D X Y; let a:=loft G A X; let K:=G.count; let w(i:Kt):= Hed u 4 K M.val (hid G A X) Y.1 i.1 D; let A':= widthCost s n*(V*wool K D)
 have hp(i:Kt): chime (fun x:Cover=> Ladder x ^n) (w i) A':= huY _ n _ _ (h _ Y.1 i.1 D v) l
 let Y' i z:= wagN n ((z,i):Mill)*‖f (z,i)‖; let U:= Ladder a; have hU:0 ≤ U:=zero_le_one.trans (ladE _)
 have hx(i): SumBudget (Y' i) (U^n*A'):=by
    let e:=Equiv.addRight (-a)
    have hv:= SBhook (hp i) e; apply SBqual (SBscale hv (t:=U^n) (pow_nonneg hU _)) (fun x=>mul_nonneg (zero_le_one.trans (wagE _ _)) (norm_nonneg _)); intro x
    have hf:‖f (x,i)‖ ≤‖w i (x-a)‖:=by unfold f ware; rw [Matrix.one_apply]; split <;> simp only [mul_one, mul_zero,norm_zero]; exact le_rfl; exact norm_nonneg _
    change (Ladder x)^n*‖f _‖ ≤ U^n * (Ladder (e x) ^n * ‖w i (e x)‖); rw [show e x=x-a from (sub_eq_add_neg ..).symm]
    refine (mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans (ladE _)) (show Ladder x ≤ U * Ladder (x-a) from ?_) n) hf (norm_nonneg _) (by have hh:=ladE (x-a); positivity)).trans_eq (by rw [mul_pow,mul_assoc]); convert wl_up a (x-a) using 1; rw [add_sub_cancel] -- tune
 let P:=fun _i:Kt=> U^n*A'; have hz:= SBprod Y' hx (show SumBudget P (∑ i:Kt,P i) from ⟨fun i=> SBgoed (hx i), (hasSum_fintype _).summable, (tsum_fintype ..).le⟩) -- tune
 apply SBmono (show SumBudget _ _ from (SBflip hz)) -- tune defin
 simp only [P,sum_const,card_univ,nsmul_eq_mul]; let BU:=usingF G X -- binder A conflict
 have he:0 ≤ A':=SBgoed (hp Y)
 apply le_trans (b:= (Fintype.card Kt:ℝ)*((9*BU)^n*A'));
 · have hh:=loft_H G A X -- f shadow tune
   exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hU hh n) he) (Nat.cast_nonneg _)
 apply le_of_eq; unfold A' K BudgetX; rw [wool_is G.count D]; unfold budT BU; ring
end Boom
end YM.CF.TableF
end
