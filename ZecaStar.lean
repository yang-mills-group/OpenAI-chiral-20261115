import ZecaMilk
import SatinThinJetsMeshes
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SatinJets.Stellar
open Function Filter Metric InnerProductSpace Set Complex
open OS.Semigroup
open scoped NNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j)(n:ℕ)
variable {s : ℝ} {a d:ℝ≥0}
variable {L:Type*}{f:Filter L}{t:L→ℝ≥0}
lemma star_conv (p:Tendsto t f (𝓝 0))(q:∀ᶠ i in f, 0< t i)(A:0<a):
    Tendsto (fun i=> mesh_diff S (t i) * S.E a) f (𝓝 (deriv S.F (duration a))):=by
 have h: Tendsto (fun i=> duration (t i)) f (𝓝[≠] 0):= by
   apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
   · simpa using! (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.comp p
   filter_upwards [q] with i e
   intro hv; exact lt_irrefl (0:ℝ) (show (0:ℂ)∈inside from (show duration (t i)=0 from hv) ▸ (dur.mpr e))
 refine ((S.localHeat _ (dur.mpr A)).differentiableAt.hasDerivAt.tendsto_slope_zero.comp h).congr' ?_
 filter_upwards [q] with i hi
 rw [show mesh_diff S (t i)* S.E a=(duration (t i))⁻¹ • (S.E (a+t i) - S.E a) by rw [add_comm,S.time]; unfold mesh_diff; rw [smul_mul_assoc,sub_mul,one_mul];rfl]; change (duration _)⁻¹ • (S.F _- S.F _) = _
 rw [show duration a+duration (t i)=duration (a+t i) by simp [duration],
     roots_heat _ A, roots_heat _ (add_pos A hi)]



-- derivative at heat coordinate (operators, not rays)
lemma stellar_pay {y:ℝ}(u:0<y):
 ‖deriv S.F (duration y.toNNReal)‖≤ 2/y:=by
 rw [duration,Real.coe_toNNReal _ u.le]
 have h : ∀ z∈Metric.ball (y:ℂ) y, z∈inside:=by
    intro z t
    rw [Metric.mem_ball,dist_comm,dist_eq_norm] at t
    have v:=(re_le_norm ((y:ℂ)-z)).trans_lt t
    rw [sub_re,ofReal_re] at v; exact (by linarith:0<z.re)
 apply norm_deriv_le_div_of_mapsTo_ball (fun z t=>
    (S.localHeat z (h z t)).differentiableAt.differentiableWithinAt) _ u
 intro z t
 rw [Metric.mem_closedBall,dist_eq_norm]
 exact (norm_sub_le ..).trans ((add_le_add (S.norm_row (h z t))
      (S.norm_row (h y (Metric.mem_ball_self u)))).trans_eq (by norm_num))

def ladle (u v:ℝ≥0)(T:H.Op):H.Op:=
 deriv S.F (duration u) * T * S.E v - S.E u * T * deriv S.F (duration v)

lemma ladle_pay {z:ℝ}(w:0<z)(T:H.Op):‖ladle S z.toNNReal z.toNNReal T‖ ≤‖T‖* (4/z):= by
 let i:=z.toNNReal
 have p:=stellar_pay S w; have r:= S.shrinks i
 have he : ‖deriv S.F (duration i) * T * S.E i‖ ≤ 2/z*‖T‖:=by
    refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) r).trans ((norm_mul_le ..).trans ?_))
    gcongr
 have hg : ‖S.E i * T * deriv S.F (duration i)‖ ≤ ‖T‖*(2/z):= by
    refine (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) r)) p (norm_nonneg _) (norm_nonneg _))
 exact (norm_sub_le ..).trans ((add_le_add he hg).trans_eq (by ring))

open YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine (Glaze_LocalFieldBounds)
def growth (z u v:ℝ≥0)(T:H.Op):= (mesh_diff S z*S.E u)*T*S.E v - S.E u*T*(mesh_diff S z*S.E v)
lemma growth_glaze {u v:ℝ≥0}(x:0<u)(y:0<v)
 (p:Tendsto t f (𝓝 0))(q:∀ᶠ i in f,0<t i) {g:L→H.Op}{T:H.Op}
 (wg:Glaze_LocalFieldBounds H f g T):
 Glaze_LocalFieldBounds H f (fun i=>growth S (t i) u v (g i)) (ladle S u v T):=by
 open YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine in
 exact (((Glaze_LocalFieldBounds.pops (star_conv S p q x)).mul wg).mul (Glaze_LocalFieldBounds.const _)).sub (((Glaze_LocalFieldBounds.const _).mul wg).mul
      (Glaze_LocalFieldBounds.pops (star_conv S p q y)))

lemma growth_eq (z u v:ℝ≥0)(T:H.Op):
 growth S z u v T=(duration z)⁻¹ •
        (S.E (u+z)*T*S.E v-S.E u*T*S.E (v+z)):= by
 unfold growth
 have hx(x:ℝ≥0):mesh_diff S z*S.E x=(duration z)⁻¹ •(S.E (x+z)-S.E x):=by
    rw [add_comm,S.time]; unfold mesh_diff; rw [smul_mul_assoc,sub_mul,one_mul];rfl
 rw [hx,hx,smul_mul_assoc,smul_mul_assoc,
     mul_smul_comm, ←smul_sub,mul_sub,
     sub_mul,sub_mul]
 abel_nf
end YM.SatinJets.Stellar
