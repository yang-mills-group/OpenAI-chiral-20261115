import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Projection
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n} {W : Type*}
-- edge orientation
abbrev dirS (s:Signed)(b:PlaqAxes):ℝ:= sign s b.val.1 * sign s b.val.2 * (if s.perm b.val.1 < s.perm b.val.2 then 1 else -1)
lemma dirS_sq(s:Signed)(b:PlaqAxes): dirS s b*dirS s b=1:=by unfold dirS StressFlux.sign; split_ifs<;>norm_num
lemma shiftOrder [AddCommGroup W][Module ℝ W](w:PlaqAxes→W)(q:PlaqAxes)(s:Signed) :
 (sign s q.val.1 * sign s q.val.2) • ((if h:s.perm q.val.1<s.perm q.val.2 then w ⟨(s.perm q.val.1,s.perm q.val.2),h⟩ else 0)-(if h:s.perm q.val.2<s.perm q.val.1 then w ⟨(s.perm q.val.2,s.perm q.val.1),h⟩ else 0)) = dirS s q • w (PlaqAxes.rotate s q):=by
 rcases q with ⟨⟨a,b⟩,h⟩; change a<b at h; have ht:=s.perm.injective.ne h.ne
 rcases lt_or_gt_of_ne ht with x|x
 all_goals simp [x,x.le,not_lt_of_gt x, PlaqAxes.rotate,PlaqAxes.ordered,dirS]
variable (s:Signed)
lemma rotateCoeff (b o : Site n) {f : Pot G n} (hG : G.Simple) (hf:p.Regular X f)
    (u:Nonwrapping X o)(hn:4 ≤ n.val)(a c:PlaqAxes):
    coeff (f ∘ Lattice.pull s b) (affine s b o) (PlaqAxes.rotate s a) (PlaqAxes.rotate s c) = dirS s a * dirS s c * coeff f o a c:=by
 let k: G.Color:=spike G; let Vv(q):= VerifiedReset.wedge q k
 have he(q:PlaqAxes): ((Vv (PlaqAxes.rotate s q)).turn s).positive = ((dirS s q) • (Vv q).positive):=by
    rw [LinearJet.positive_turn]; unfold reframe Vv; funext i; rw [orderedDir,orderedDir,shiftOrder,Pi.smul_apply,curl_wedge,curl_wedge]; by_cases h:i=q; · subst i; simp
    rw [if_neg (show PlaqAxes.rotate s q ≠ PlaqAxes.rotate s i from (PlaqAxes.transform s).injective.ne (Ne.symm h)), if_neg (Ne.symm h),smul_zero,smul_zero]
 let VF(a):= VerifiedReset.wedge a (dirS s a • k); have hu(q): ((Vv (PlaqAxes.rotate s q)).turn s).positive=(VF q).positive:=by
    rw [he]; unfold Vv VF; funext t; rw [Pi.smul_apply,curl_wedge,curl_wedge]; change _ • (if _ then _ else _) = if _ then _ else _; split; rfl; exact smul_zero _
 change logHessian _ ((wedge _ (spike G)).field _) ((wedge _ (spike G)).field _) = _
 rw [(Vv (PlaqAxes.rotate s a)).hessian_turn s _ _ u hn _ hG hf, LinearJet.hessian_curl hG hf u hn (hu a) (hu c), label_color o hG hf a c]; rw [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq]; unfold k; rw [spike_norm hG]; ring
end YM.AnalyticBridge.VerifiedReset
