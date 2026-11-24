import SatinThinJetsAnalytic
import YM.SU5.Six.Night
/-!
# A jet in time is a **fixed order** limit of shrinking intrinsic differences

Below no preassigned decay rate tying the size of the forward differences to the
convergence of the underlying marks. Exploit op-norm control at positive heat.
-/
set_option autoImplicit false
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
-- One true mesh step
def mesh_diff (d:ℝ≥0): H.Op:= (duration d)⁻¹ • (S.E d-1)
lemma mesh_step (v:H): mesh_diff S d v=(duration d)⁻¹ • (S.E d v-v):= rfl
private lemma mesh_heat : Commute (mesh_diff S d) (S.E a):= by
  have hp: Commute (S.E d) (S.E a):= Eq.trans (S.time d a).symm (add_comm d a ▸ S.time a d)
  exact ((hp.sub_left (Commute.one_left _)).smul_left _)
private lemma bundled : (mesh_diff S d)^n*S.E (n • a)=(mesh_diff S d * S.E a)^n:= by
 rw [clock_mul, Commute.mul_pow (mesh_heat S)]
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

variable (Y : ℝ → H)(h:Positive S Y)
/-- A shrinking grid suffices, even for varying vectors converging only in norm at positive time. -/
def Operates (e:L→ℝ→ H): Prop :=
  (∀ s:ℝ,0<s→ Tendsto (fun i=> e i s) f (𝓝 (Y s))) ∧
  ∀ (s:ℝ)(d:ℝ≥0),0<s→ ∀ᶠ i in f, e i (s+(d:ℝ))= S.E d (e i s)
include h
private lemma jet_power (s:ℝ)(u:0<s)(t:ℝ≥0)(p:0<t):
    jet S Y n (↑(s+ ↑(n • t):ℝ):ℂ)= (deriv S.F (duration t) ^ n) (Y s):= by
 induction n with
 | zero=> simpa [jet] using lifted_heat S Y h u
 | succ i ih =>
   rw [show s+ ↑((i+1) • t)= (t:ℝ)+(s+↑(i • t)) from (by simp; ring), ofReal_add, jet_tick S Y h i (duration t) _ (dur.mpr p) (show 0<(↑(s+ ↑(i • t):ℝ):ℂ).re from add_pos_of_pos_of_nonneg u (NNReal.zero_le_coe ..)),ih,pow_succ']
   rfl
private lemma multi_time {s:ℝ}(p:0<s)(n:ℕ): ∃ (s₀:ℝ)(a:ℝ≥0),0<s₀∧0<a∧ s=s₀+ ↑(n • a):=by
 let t:= s/((n:ℝ)+1); have ht:0<t:=div_pos p (by positivity)
 refine ⟨t, t.toNNReal,ht,Real.toNNReal_pos.mpr ht,?_⟩
 simp only [NNReal.coe_natCast, NNReal.coe_mul,Real.coe_toNNReal _ ht.le, nsmul_eq_mul]; unfold t; field_simp; ring
lemma mesh_limit (A:L→ ℝ→ H)(w:Operates (f:=f) S Y A)(p:Tendsto t f (𝓝 0))
    (q:∀ᶠ i in f,0< t i)(hs:0<s):
    Tendsto (fun i:L=> ((mesh_diff S (t i))^n) (A i s)) f (𝓝 (jet S Y n s)):=by
 obtain ⟨a,d,ha,hd,rfl⟩:= multi_time S Y h hs n
 rw [jet_power S n Y h _ ha _ hd]
 let g (i:L):=(mesh_diff S (t i)* S.E d)^n; let m:= (deriv S.F (duration d))^n
 have hp:= diff_conv S p q hd |>.pow n
 have hT:Tendsto (fun i=>g i (A i a)) f (𝓝 (m (Y a))):=
     (Continuous.clm_apply (show Continuous (@Prod.fst H.Op H) from continuous_fst) continuous_snd |>.continuousAt.tendsto).comp (hp.prodMk_nhds (w.1 a ha))
 refine hT.congr' ((w.2 a (n • d) ha).mono fun i e=>?_); dsimp only; rw [e]; unfold g; rw [← bundled]; rfl

-- plain exact heat, incl any finite step. Expose the chain /
lemma Positive.moves {s:ℝ}(p:0<s)(t:ℝ≥0) : Y (s+(t:ℝ))= S.E t (Y s):= by rw [h _ (s+ t) p (by simp),add_sub_cancel_left,Real.toNNReal_coe]
lemma jet_positive: Positive S (fun s=>jet S Y n (s:ℂ)):= by
 intro s t p q; rcases lt_or_eq_of_le q with w|w
 · change jet S Y n (t:ℂ)=_
   rw (occs:=.pos [1]) [show (t:ℂ)=(↑(t-s):ℂ)+↑s by simp]
   rw [jet_shift S Y h n (show 0<(↑(t-s):ℂ).re from sub_pos.mpr w) (show (s:ℂ)∈inside from p), branch_eq_heat S _ (sub_pos.mpr w)]
 rw [w,sub_self,Real.toNNReal_zero,S.eZero]; rfl
omit h
lemma mesh_dark(v:H): S.orth (mesh_diff S d v)=0:= by
 refine (Submodule.starProjection_apply_eq_zero_iff ..).mpr ((S.ground.mem_orthogonal' _).mpr fun w p=> ?_)
 rw [mesh_step,inner_smul_left,inner_sub_left,S.swing,(S.fixed _).mp p,sub_self,mul_zero]
lemma mesh_night (S : OS.Semigroup H timeAxis)(v:H): S.ℚmeasure.region Six.night (mesh_diff S d v)=0:= by
 rw [mesh_diff, show S.E d-1= -(1-S.E d) from (by abel)]
 change S.ℚmeasure.region Six.night ((duration d)⁻¹ • (- ((1-S.E d:H.Op) v)))=_; rw [map_smul,map_neg,Six.morning,neg_zero,smul_zero]

include h
lemma exact_run {s:ℝ} (u:0<s)(p:Tendsto t f (𝓝 0)) (q:∀ᶠ i in f, 0< t i): Tendsto (fun i=> ((mesh_diff S (t i))^n) (Y s)) f (𝓝 (jet S Y n s)):=
 mesh_limit S n Y h _ ⟨fun _ _=>tendsto_const_nhds,fun _ t u=> Eventually.of_forall fun _=> Positive.moves S Y h u t⟩ p q u
private def dimes (i:ℕ):ℝ≥0 := 1/((i:ℝ≥0)+1)
private lemma dark_by_conv (P:H.Op)(p:∀ (t:ℝ≥0)(v:H),P (mesh_diff S t v)=0)(u:0<s):
    P (jet S Y (n+1) s)=0:=by
 have hT:= P.continuous.continuousAt.tendsto.comp (exact_run S (n+1) Y h u (t:=dimes) (f:=atTop) (NNReal.tendsto_coe.mp (by simpa only [Function.comp_def, dimes,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one, NNReal.coe_zero] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))) (Eventually.of_forall fun i=> by unfold dimes; positivity))
 apply tendsto_nhds_unique hT (tendsto_const_nhds.congr (fun i=>?_)); dsimp only [Function.comp]; rw [pow_succ']; exact Eq.symm (p _ _)
lemma jet_dark (u:0<s): S.orth (jet S Y (n+1) s)=0:= dark_by_conv S n Y h _ (fun _=>mesh_dark S) u
omit h
lemma jet_night (S : OS.Semigroup H timeAxis)(h:Positive S Y)(u:0<s): S.ℚmeasure.region Six.night (jet S Y (n+1) s)=0:= dark_by_conv S n Y h _ (fun _=>mesh_night S) u
end YM.SatinJets
#print axioms YM.SatinJets.jet_night
#print axioms YM.SatinJets.jet_positive
#print axioms YM.SatinJets.jet_dark
#print axioms YM.SatinJets.mesh_limit
