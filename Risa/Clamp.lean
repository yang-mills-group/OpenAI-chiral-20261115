import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace Virgo
open Function Real Filter
open scoped Topology NNReal InnerProductSpace
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E] (c:ℝ)
abbrev coil (v:E):=c^2 + ‖v‖^2
def clipQ(v:E):ℝ:=c^2 * (‖v‖^2) / coil c v
lemma clip_pos(h:0<c)(v:E): 0 ≤ clipQ c v:=by unfold clipQ coil; positivity
lemma clip_le(h:0<c)(v:E): clipQ c v ≤ c^2:=by
 have p:0< coil c v:=by unfold coil; positivity
 unfold clipQ; rw [div_le_iff₀ p]; unfold coil; nlinarith [sq_nonneg (c^2)]
lemma clip_diff (h:0<c): ContDiff ℝ 1 (fun i:E=>clipQ c i):= by
 have hc:ContDiff ℝ 1 (fun i:E=>‖i‖^2):=by simp_rw [← real_inner_self_eq_norm_sq]; exact contDiff_id.inner ℝ contDiff_id -- tune
 exact (((contDiff_const (c:=c^2)).mul hc).div (contDiff_const.add hc) (fun i:E=> ne_of_gt (show 0<c^2+‖i‖^2 by positivity)))
lemma coil_price (h:0<c)(v:E): ‖v‖^4/(coil c v) ≤ c⁻¹^2*‖v‖^4:=by unfold coil; have hp:0<c^2:=sq_pos_of_pos h; field_simp; nlinarith [mul_nonneg (show 0≤‖v‖^4 by positivity) (sq_nonneg ‖v‖)]
lemma recoil(h:0<c)(v:E): |‖v‖^2-clipQ c v|≤ c⁻¹^2*‖v‖^4:=by
 have hp:0<coil c v:=by unfold coil; positivity
 apply le_trans _ (coil_price _ h v); unfold clipQ; rw [show ‖v‖^2-c^2*‖v‖^2/coil c v=‖v‖^4/coil c v from (?_), abs_of_nonneg (by positivity)]; unfold coil; field_simp; ring
lemma clip_lift(h:0<c)(v w:E): |clipQ c v-clipQ c w|≤2*c*‖v-w‖:=by
 let a:=‖v‖; let b:=‖w‖; have hv:0 ≤ a:=norm_nonneg v; have hw:0 ≤ b:=norm_nonneg w; let d:= ‖v-w‖
 let p:=coil c v; let q:=coil c w; have hp:p=c^2+a^2:=rfl; have hq:q=c^2+b^2:=rfl
 have ph:c^2  ≤ p:=by rw [hp]; linarith [sq_nonneg a]
 have pq:c^2  ≤ q:=by rw [hq]; linarith [sq_nonneg b]
 have p1:0 < p:=(sq_pos_of_pos h).trans_le ph; have q1:0<q:= (sq_pos_of_pos h).trans_le pq
 have he: clipQ c v-clipQ c w= c^4*(a-b)*(a+b)/(p*q):=by
    unfold clipQ; change c^2*a^2/p-c^2*b^2/q=_; field_simp; rw [hp,hq]; ring
 rw [he,abs_div,abs_of_pos (mul_pos p1 q1),abs_mul,abs_mul,abs_of_nonneg (add_nonneg hv hw),abs_of_nonneg (pow_nonneg h.le _), div_le_iff₀ (mul_pos p1 q1)]
 have h: c^3*a ≤ c^2*p:=by
    have h': c*a ≤ p := by rw [hp]; nlinarith [sq_nonneg (a-c)]
    nlinarith only [mul_le_mul_of_nonneg_left h' (sq_nonneg c)]
 have h2:c^3*b ≤ c^2*q:=by
    have h': c*b ≤ q :=by rw [hq]; nlinarith [sq_nonneg (b-c)]
    nlinarith only [mul_le_mul_of_nonneg_left h' (sq_nonneg c)]
 have h3: c^3*(a+b) ≤2*(p*q):=by nlinarith only [h,h2,mul_le_mul_of_nonneg_right ph q1.le,mul_le_mul_of_nonneg_right pq p1.le]
 have ha: |a-b| ≤ d:= abs_norm_sub_norm_le v w
 have hv:0 ≤ c:=by linarith only [‹0<c›]
 nlinarith only [mul_le_mul_of_nonneg_left ha (show 0 ≤ c^4*(a+b) from mul_nonneg (pow_nonneg hv _) (add_nonneg (norm_nonneg _) hw)),mul_le_mul_of_nonneg_left h3 (show 0 ≤ c*d from mul_nonneg hv (norm_nonneg _))]
#print axioms clip_lift
end Virgo
