import YM.SU5.Registration.Heave.AirCarry
import YM.SU5.Same.TemperPrism
/-!
Use at every induction step, keep estimate polynomial. Adapted word-for-word
mesh helpers from `SatinThinJetsMeshes`. Work on strictly positive heat.
# A jet in time is a **fixed order** limit of shrinking intrinsic differences

Below no preassigned decay rate tying the size of the forward differences to the
convergence of the underlying marks. Exploit op-norm control at positive heat.
-/
set_option maxHeartbeats 220000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j)(n:ℕ)
variable {s : ℝ} {a d:ℝ≥0}
namespace Drums
private lemma mesh_heat : Commute (mesh_diff S d) (S.E a):= by
  have hp: Commute (S.E d) (S.E a):= Eq.trans (S.time d a).symm (add_comm d a ▸ S.time a d)
  exact ((hp.sub_left (Commute.one_left _)).smul_left _)
private lemma mesh_form: mesh_diff S d * S.E a=(duration d)⁻¹ • (S.E (a+d) - S.E a):= by
 rw [add_comm, S.time]; unfold mesh_diff; rw [smul_mul_assoc,sub_mul,one_mul]; rfl
variable {L:Type*}{f:Filter L}{t:L→ℝ≥0}
private lemma diff_conv (p:Tendsto t f (𝓝 0))(q:∀ᶠ i in f, 0< t i)(A:0<a):
    Tendsto (fun i=> mesh_diff S (t i) * S.E a) f (𝓝 (deriv S.F (duration a))):=by
 have h: Tendsto (fun i=> duration (t i)) f (𝓝[≠] 0):= by
   apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
   · simpa using! (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.comp p
   filter_upwards [q] with i e
   intro hv; exact lt_irrefl (0:ℝ) (show (0:ℂ)∈inside from (show duration (t i)=0 from hv) ▸ (dur.mpr e))
 refine ((S.localHeat _ (dur.mpr A)).differentiableAt.hasDerivAt.tendsto_slope_zero.comp h).congr' ?_
 filter_upwards [q] with i hi
 rw [mesh_form]; change (duration _)⁻¹ • (S.F _- S.F _) = _
 rw [show duration a+duration (t i)=duration (a+t i) by simp [duration],
     roots_heat _ A, roots_heat _ (add_pos A hi)]
open _root_.YM.SatinRegistration
open _root_.YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine (deriv_heat_cost RisePrice)
lemma gatherDiff {d:ℝ≥0}(B:H.Op) : (duration d)⁻¹ • (S.E d * B - B * S.E d)= mesh_diff S d * B- B * mesh_diff S d:=by
 unfold mesh_diff; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,sub_mul,one_mul,mul_sub,mul_one]; simp_rw [smul_sub]; abel -- no need a
lemma gatherDiff₁ (d:ℝ≥0)(B:H.Op) : (duration d)⁻¹ • (S.E d * B - B * S.E d)= mesh_diff S d * B- B * mesh_diff S d:= gatherDiff S B

abbrev genPrice (a:ℝ≥0):= deriv S.F (duration a)
def action (a:ℝ≥0)(G U:H.Op): H.Op := G*U*S.E a-S.E a*U*G
lemma raw_action (a d:ℝ≥0)(B:H.Op) :
    (duration d)⁻¹ • (S.E d * (S.E a* B * S.E a) - (S.E a* B * S.E a) * S.E d)= action S a (mesh_diff S d*S.E a) B:=by
 rw [gatherDiff₁]; unfold action; rw [←mul_assoc (mesh_diff S d), ←mul_assoc (mesh_diff S d), mul_assoc (S.E a*B), (mesh_heat S).symm.eq]
lemma limit_action (d:ℕ→ℝ≥0)(u:Tendsto d atTop (𝓝 0))(v:∀ᶠ i:ℕ in atTop, 0<d i){U:ℕ→H.Op}{B:H.Op}(p:Flying U B) (a:ℝ≥0)(z:0<a) :
    Flying (fun i=> action S a (mesh_diff S (d i) * S.E a) (U i)) (action S a (genPrice S a) B):=by
 let h:= Flying.by_norm (diff_conv S u v z)
 let f:= Flying.still (S.E a)
 exact ((h.multiply p).multiply f).sub' ((f.multiply p).multiply h)
lemma fare_action (d:ℕ→ℝ≥0)(u:Tendsto d atTop (𝓝 0))(v:∀ᶠ i:ℕ in atTop, 0<d i){U:ℝ≥0→ℕ→H.Op}(p:RisePrice U) : RisePrice (fun t i => action S (t/2) (mesh_diff S (d i)* S.E (t/2)) (U (t/2) i)):=by
 obtain ⟨k,C,b,p⟩:=p
 refine ⟨k+1,2^(k+1)*(2*3*C),by positivity,fun t x z=>?_⟩
 let a:= t/2; have hx:0<a:=half_pos x
 have hx':0<(a:ℝ):=hx
 let D:=1/((a:ℝ)/2); have hD: D < 3/(a:ℝ):=by unfold D; field_simp; linarith
 let B(i):= mesh_diff S (d i)*S.E a
 have h:‖genPrice S a‖ ≤ D:= deriv_heat_cost S (duration a) hx'
 filter_upwards [p a hx ((half_lt_self x).le.trans z), (diff_conv S u v hx).norm.eventually (ge_mem_nhds (h.trans_lt hD))] with i hB hv
 let F:= B i; let X:= U a i; let w:= ‖X‖
 change _*‖action S a F X‖≤ _
 have ha:‖action S a F X‖≤ 2*(w*(3/(a:ℝ))) := by
    apply (norm_sub_le ..).trans; rw [two_mul]; have hx:‖F‖≤3/(a:ℝ):=hv; apply add_le_add
    · rw [mul_comm w]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (S.shrinks a)).trans ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))))
    exact (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks a))) hx (norm_nonneg _) (norm_nonneg _))
 refine (mul_le_mul_of_nonneg_left ha (pow_nonneg (show (0:ℝ) ≤ (t:ℝ) by positivity) _)).trans ?_  -- x NNReal coe
 have ht:(t:ℝ)=2*(a:ℝ):=by unfold a; rw [NNReal.coe_div,NNReal.coe_ofNat]; ring
 rw [ht, mul_pow,mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (by positivity)
 rw [show (a:ℝ)^(k+1)*(2*(w*(3/(a:ℝ))))= 2*3*((a:ℝ)^k*w) from (by field_simp; ring)]
 linarith only [show (a:ℝ)^k*w ≤ _ from hB]
end Drums
#print axioms Drums.raw_action
#print axioms Drums.limit_action
#print axioms Drums.fare_action
end YM.SatinJets
