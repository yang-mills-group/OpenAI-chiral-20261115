import Risa.Verdant
import Risa.Snag
import Risa.Variance
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
open Almanac CF.BProof
variable (Qh:Hike) (y:ℝ)(Rs:Rules G)(Lc:Side)
local notation "χ"=> Qh.cost
local notation "Γ"=> (ridges:ℝ)
local notation "𝕥"=>p.threshold
local notation "τh"=>tempRate p Qh y
local notation "Υ₀"=>posess G Qh
universe w0
-- SOil smooth Ga estimates.Cluster c at fixed election, orientation accounting.
variable {I Ux:Type}[Fintype I][Fintype Ux](o:I×Ux→Bool→ Site n)(t:I×Ux→Bool→Signed)(n₀:Bool)(a c':ℝ) (p1:BudgetPoint)
noncomputable abbrev mealSeat (G:Gauge)(p:BudgetPoint)(y:ℝ)(o:I×Ux→Bool→Site n)(t:I×Ux→Bool→Signed)(n₀:Bool)(a c':ℝ)(i:I)(V:Config G n):ℝ:=∑ j:Ux,a*(raiseX G p y n₀ V (t (i,j)) (o (i,j))-c')
lemma seat_env (i:I):Envelope (mealSeat G p1 y o t n₀ a c' i):=by
 unfold mealSeat; simp_rw [sub_eq_add_neg]; apply Envelope.sum univ (fun j x=> a*(raiseX G p1 y n₀ x (t (i,j)) (o (i,j)) + -c')); intro j; refine (Envelope.const _).mul (Envelope.add ?_ (Envelope.const _)); unfold raiseX loader; split; exact (launch_env ..).mul (launch_env ..); exact launch_env ..
abbrev merrymark(s:Bool):ℝ:= if s then 1 else -1
@[simp] lemma merrymark_eval(s:Bool): |merrymark s|=1:=by unfold merrymark; cases s <;> simp
-- assume exponential bound hR after calendar invocation. 
variable (W:Config G n→ℝ)(hW:Envelope W)(hw:∀ x,0 ≤ W x)
include hw hW
lemma liveSeat {Q0 v:ℝ} (hR:∀ Z:I→Bool,let k:=fun i:I=> merrymark (Z i)
  (∫ x:Config G n,W x*Real.exp (tables G p1 y o t (fun i=>a*k i.1) n₀ x)∂prior G n) ≤ Real.exp (Q0+∑ i:I×Ux, (a*k i.1)*v))
 (hc:|v-c'| *|a| *(Fintype.card Ux:ℝ)≤ 1): (∫ x:Config G n, W x*∏ i:I, |mealSeat G p1 y o t n₀ a c' i x| ∂prior G n) ≤ Real.exp (Q0+ (1+Real.log 2)*(Fintype.card I:ℝ)):=by
 let S(i:I):=mealSeat G p1 y o t n₀ a c' i
 let E:Type:= I→Bool
 let f(e:E):= tables G p1 y o t (fun i=>a*merrymark (e i.1)) n₀
 let D(e:E)(x:Config G n):=∑ i:I,merrymark (e i)* S i x
 have hf (x:Config G n): W x*∏ i:I, |S i x| ≤∑ e:E,W x*Real.exp (D e x):=by
    let e(i:I):Bool:=decide (0≤ S i x)
    refine (show W x*∏ i:I,|S i x| ≤ W x* Real.exp (D e x) from ?_).trans (single_le_sum (f:=fun i:E=>W x*Real.exp (D i x)) (fun _ _=> mul_nonneg (hw _) (Real.exp_pos _).le) (mem_univ e))
    unfold D; rw [Real.exp_sum]; refine mul_le_mul_of_nonneg_left (prod_le_prod (fun i _=>abs_nonneg _) fun i _=>?_) (hw _)
    have ht(i:I):merrymark (e i)*S i x=|S i x|:=by
       by_cases t:0 ≤ S i x; · simp [t,e,merrymark,abs_of_nonneg]
       simp [t,e,merrymark,abs_of_neg (lt_of_not_ge t)]
    rw [ht]; exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
 have he(i:I):Envelope (S i):=seat_env y o t n₀ a c' p1 i
 have hd(e:E):Envelope (D e):= Envelope.sum univ (fun i x=>merrymark (e i)* S i x) (fun i=> (Envelope.const _).mul (he i))
 have hg(e:E):Integrable (fun x=> W x * Real.exp (D e x)) (prior G n):=(hW.mul ((hd e).exp)).integrable _
 refine (integral_mono_of_nonneg (Eventually.of_forall (fun i=> mul_nonneg (hw _) (prod_nonneg (fun i _=> abs_nonneg _)))) (integrable_finsetSum _ (fun i h=> hg i)) (Eventually.of_forall hf)).trans ?_
 rw [integral_finsetSum _ (fun i h=>hg i)]
 let N(i:I×Ux):ℝ:= 1; let V(e:E)(i:I×Ux):= a*merrymark (e i.1); let b(e:E):=∑ i:I×Ux,V e i*c'; let d(e:E):=∑ i:I×Ux,V e i*v
 let T:ℝ:=Fintype.card I; let L:ℝ:=Fintype.card Ux
 have hs(e:E):d e - b e ≤ T:=by
    have hp(i:I×Ux): V e i*v- V e i*c' ≤ |v-c'| *|a|:= by
       unfold V; apply (le_abs_self _).trans (le_of_eq _); rw [← mul_sub_left_distrib, abs_mul,abs_mul,merrymark_eval,mul_one,mul_comm]
    unfold d b; rw [←sum_sub_distrib]; refine (Finset.sum_le_sum (g:=fun _=> |v-c'| *|a|) (fun i _=>hp i)).trans ?_
    · simp [Fintype.card_prod]; change (T*L)*_ ≤ _; linarith only [mul_le_mul_of_nonneg_left hc (show 0≤T from Nat.cast_nonneg _)]
 have hi(e:E):(∫ x:Config G n,W x*Real.exp (D e x)∂prior G n) ≤ Real.exp (Q0+T):=by
    have hDec(x:Config G n): D e x=f e x-b e:=by
       unfold D f tables S mealSeat b V; rw [Fintype.sum_prod_type,Fintype.sum_prod_type,←sum_sub_distrib]; apply sum_congr rfl; intro i _; rw [Finset.mul_sum,←sum_sub_distrib]; exact sum_congr rfl fun _ _=> (by ring)
    have hx(x:Config G n): W x*Real.exp (D e x)=Real.exp (-b e)*(W x * Real.exp (f e x)):=by rw [hDec,sub_eq_add_neg,Real.exp_add]; ring
    simp_rw [hx]; rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left (hR e) (Real.exp_pos _).le).trans ?_; change Real.exp (-b e)*Real.exp (Q0+d e)≤_; rw [←Real.exp_add]; exact Real.exp_monotone (by linarith only [hs e])
 refine (sum_le_sum (fun i _=> hi i)).trans_eq ?_; rw [sum_const,card_univ,nsmul_eq_mul,show Fintype.card E=2^Fintype.card I from (by unfold E; rw [Fintype.card_fun,Fintype.card_bool]),show Q0+(1+Real.log 2)*T=(Fintype.card I:ℝ)*Real.log 2+(Q0+T) from (by unfold T; ring),Real.exp_add (_*Real.log 2) (Q0+T),Real.exp_nat_mul,Real.exp_log two_pos]; push_cast; rfl -- tune
#print axioms liveSeat
end Risa
end YM.Gleam.Luster
