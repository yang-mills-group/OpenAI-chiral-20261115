import YM.CF.Continuum.Billhead
import YM.Push.BETA_TRANSPORT.Curve
set_option synthInstance.maxSize 25000
set_option maxHeartbeats 750000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph.Angle
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial RG Skye Laic MeasureTheory Cascade Flare
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{a C L b c δ v:ℝ}{Q:PathData SU.group}{F:Clip}
def pivotTax (P:BudgetPoint)(n:Side)(F:Clip)(C:ℝ):= Fintype.card (Face (Per n)) * (F.direct*2 + F.linear * P.threshold * 2 + (C*2)^2/2)
def jumpTax (P:BudgetPoint)(n:Side)(F:Clip)(C:ℝ):= pivotTax P n F C + n.val^4 * (C*P.threshold^3+C*P.threshold^4) -- exact scale at β, huge if threshold small still ok. include multiplication casts
variable {e:ℝ} (V:Wilson.Config SU.group n)
lemma pivot_B (h:Q.Bounds F a C L)(hp:0≤ C)(i:Face (Per n)) : ‖Q.baseTerm F P V i‖≤ F.direct*2+ F.linear*P.threshold*2 +(C*2)^2/2:=by
 have hx:= P.threshold_pos; have hb:=F.tail_pos; have hw:=F.quadratic_pos; let x:= group.chord (faceValue V i); have ht:0≤ x:= SU.group.chord_nonneg _; have hs:x≤2:= SU.group.chord_le_two _; have hz: x^2 ≤ 2^2:= pow_le_pow_left₀ ht hs 2
 unfold PathData.baseTerm; refine (norm_add_le ..).trans (add_le_add ?_ ?_)
 · change ‖PathData.clipped F _ x‖ ≤ _; unfold PathData.clipped; split; next h=> rw [Real.norm_of_nonneg (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hz hw.le,mul_pos hb hx]
   rw [Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans (le_add_of_nonneg_left (by positivity))
 split; next h_e => rw [Real.norm_of_nonneg (by positivity)]; exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (pea h V (fun i=> SU.group.chord_le_two _) (by positivity) _) 2) (by norm_num)
 rw [norm_zero]; positivity
lemma kinetic_P (h:Q.Bounds F a C L)(g:0≤C) : |Push.BetaTransport.kinetic Q F P V| ≤ jumpTax P n F C:=by
 have hp (V:Wilson.Config group n) : ‖ (∑ i:Face (Per n),Q.baseTerm F P V i)+∑ x:Site n,(PathData.atomSeries Q.cubic P V x + PathData.atomSeries Q.quartic P V x)‖ ≤ jumpTax P n F C:=by
    refine (norm_add_le ..).trans (add_le_add ?_ (oath h P V).1); exact (norm_sum_le ..).trans ((sum_le_sum (fun i _=> pivot_B V h g i)).trans_eq (by unfold pivotTax; rw [sum_const,card_univ,nsmul_eq_mul]))
 exact sealV _ (fun i=>hp (pull i 0 V)) -- braces?
lemma jump_delta (h:Q.Bounds F a C L)(g:0≤C) (p:|b-c|≤δ): |Q.inChannels F P b V-Q.inChannels F P c V|≤δ * jumpTax P n F C :=by
 rw [Push.BetaTransport.channels_split V b, Push.BetaTransport.channels_split V c, add_sub_add_right_eq_sub, ← sub_mul, abs_mul]; exact mul_le_mul p (kinetic_P V h g) (abs_nonneg _) ((abs_nonneg _).trans p)
variable {U V':GramM n} -- gauge scale More n below.
local notation "Yκ" => jumpTax U.p (More n) U.funds C
lemma arcshift (X:Pane n)(h:U.path.Bounds U.funds a C L)(g:0≤C)(p:|U.beta-V'.beta|≤δ) (t:δ * jumpTax U.p (More n) U.funds C≤1/2)(u:U.p=V'.p)(v:U.path=V'.path)(q:U.funds=V'.funds) : |past U X-past V' X| ≤ past V' X*(2*(δ*jumpTax U.p (More n) U.funds C)):=by
 let x:=U.path.inChannels U.funds U.p U.beta X; let y:=U.path.inChannels U.funds U.p V'.beta X; let z:= -x+y; have he:x-y=-z:=by unfold z; abel
 have hh:|z|≤δ*jumpTax U.p (More n) U.funds C:=by have hh:= jump_delta X h g (P:=U.p) p; rw [show U.path.inChannels U.funds U.p U.beta X - U.path.inChannels U.funds U.p V'.beta X=-z from he, abs_neg] at hh; exact hh
 let A:=past V' X; have hF:past U X=A*Real.exp z:=by unfold A past; rw [←v, ←q, ←u, ←Real.exp_add]; change Real.exp (-x)= _; unfold z; congr 1; change -x=-y+_; ring
 rw [hF, ←mul_sub_one,abs_mul,abs_of_nonneg (show 0 ≤ past V' X from (Real.exp_pos _).le)] -- hb A let not changed rewrite
 apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
 have hf:= Complex.norm_exp_sub_one_le (x:=(z:ℂ)) (show ‖(z:ℂ)‖≤1 from (Complex.norm_real _).le.trans ((show |z|≤(1:ℝ) from hh.trans (le_trans t (by norm_num)))))
 rw [←Complex.ofReal_exp, ←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs] at hf; exact hf.trans (by linarith)
end YM.CF.Graph.Angle
