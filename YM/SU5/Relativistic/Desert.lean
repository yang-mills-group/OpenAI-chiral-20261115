import YM.SU5.Relativistic.Boulevards
import YM.SU5.Relativistic.Quintile
/-! # disappearance of stamp evolute coefficients implies no eigenfunctions. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.Signs
open Filter Function MeasureTheory Metric Set InnerProductSpace ContinuousLinearMap
open scoped Topology NNReal InnerProductSpace ComplexOrder
open CF.Buffered.Afterglow.Tower.Vacancy HostLegal
variable {H:Hilbert}
lemma evaporates (P:Rolls H)(ξ η:H) {K:ℤ→ℤ→ℂ}(u:Stock K P ξ η)(p:Tendsto (fun n:ℕ×ℕ=> K n.1 n.2) atTop (𝓝 0)): Tendsto (fun i:ℕ=>inner ℂ ξ (P.wind i η)) atTop (𝓝 0):=by
 apply Metric.tendsto_nhds.mpr; intro ε e
 obtain ⟨N,Q⟩:= eventually_atTop.mp (Metric.tendsto_nhds.mp p (ε/2) (by positivity))
 obtain ⟨k,v,h⟩:=((u (ε/2) (by positivity)).and (eventually_ge_atTop N.1)).exists
 filter_upwards [eventually_ge_atTop N.2] with n z
 rw [dist_comm]; apply (dist_triangle 0 (K k n) _).trans_lt; rw [dist_comm 0]
 exact (add_lt_add (Q (k,n) ⟨h,z⟩) (v (n:ℤ))).trans_eq (add_halves ..)

lemma sterile (P:Rolls H)(S:H.Op)(s:Set H)(hs:Dense s)
  (p:∀ x∈s,Tendsto (fun i:ℕ=> inner ℂ (S x) (P.wind i x)) atTop (𝓝 0)) (x:H) :
  Tendsto (fun i:ℕ=> inner ℂ (S x) (P.wind i x)) atTop (𝓝 0):=by
 let E(δ:ℝ):= δ*‖S‖*(δ+2*‖x‖)
 apply Metric.tendsto_nhds.mpr; intro ε hε
 have e:Tendsto E (nhdsWithin 0 (Ioi 0)) (𝓝 0):=by
    have hp:Continuous E:= by unfold E; fun_prop
    have h0:Tendsto E (nhdsWithin 0 (Ioi 0)) (𝓝 (E 0)):= (hp.tendsto _).mono_left nhdsWithin_le_nhds; rwa [show E 0=0 from (by unfold E; ring)] at h0
 -- alternative
 obtain ⟨d,v,w⟩:= (Eventually.and (show ∀ᶠ i in nhdsWithin 0 (Ioi (0:ℝ)), i ∈ Ioi 0 from self_mem_nhdsWithin) (e.eventually (gt_mem_nhds (by linarith: ε/2 > 0)))).exists
 have ht:0<d:= v
 obtain ⟨y,q,t⟩:= Metric.mem_closure_iff.mp (hs x) d ht
 filter_upwards [Metric.tendsto_nhds.mp (p y q) (ε/2) (by positivity)] with n r
 apply (dist_triangle _ (inner ℂ (S y) (P.wind n y)) 0).trans_lt; refine (add_lt_add (_root_.lt_of_le_of_lt ?_ w) r).trans_eq (add_halves ..)
 rw [dist_eq_norm]; rw [dist_eq_norm] at t
 let V:= P.wind n
 change ‖inner ℂ (S x) (V x) - inner ℂ (S y) (V y)‖≤_
 rw [show inner ℂ (S x) (V x) - inner ℂ (S y) (V y)=inner ℂ (S (x-y)) (V x)+inner ℂ (S y) (V (x-y)) from (by rw [map_sub,map_sub,inner_sub_left,inner_sub_right]; ring)]
 refine le_trans (norm_add_le _ _) ?_
 have hv : ‖V x‖=‖x‖:=P.solid ..; have hw: ‖V (x-y)‖≤d:=(P.solid ..).trans_le t.le
 have HA:‖S (x-y)‖ ≤ ‖S‖*d:= (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left t.le (norm_nonneg _))
 have HB: ‖S y‖≤ ‖S‖*(‖x‖+d):=(S.le_opNorm _).trans (mul_le_mul_of_nonneg_left (by have hg:= norm_sub_norm_le y x; rw [norm_sub_rev] at hg; linarith) (norm_nonneg _))
 exact (add_le_add ((norm_inner_le_norm ..).trans (mul_le_mul HA hv.le (norm_nonneg _) ((norm_nonneg _).trans HA))) ((norm_inner_le_norm ..).trans (mul_le_mul HB hw (norm_nonneg _) ((norm_nonneg _).trans HB)))).trans_eq (by unfold E; ring)
lemma dies (P:Rolls H) (x:H)(p:Tendsto (fun i:ℕ=> inner ℂ x (P.wind i x)) atTop (𝓝 0))(z:ℂ)(v:P.wind 1 x=z • x):x=0:=by
 have h(i:ℕ): P.wind i x=z^i • x:= by
    induction i with| zero=>rw [Nat.cast_zero,P.nil,pow_zero,one_smul]; rfl| succ i ih=> rw [Nat.cast_add_one,← P.along,ContinuousLinearMap.comp_apply,v,map_smul,ih,smul_smul,pow_succ']
 have hp:Tendsto (fun i:ℕ=> ‖inner ℂ x (P.wind i x)‖) atTop (𝓝 0):= by simpa using p.norm
 by_contra t
 have h':‖x‖≠0:=by rwa [Ne, norm_eq_zero]
 have hz:‖z‖=1:=by have ht:=P.solid 1 x; rw [v,norm_smul] at ht; exact (mul_eq_right₀ h').mp ht -- tune
 have he(i:ℕ):‖inner ℂ x (P.wind i x)‖=‖x‖^2:= by rw [h,inner_smul_right,norm_mul,norm_pow,hz,one_pow,one_mul,inner_self_eq_norm_sq_to_K,norm_pow]; simp
 exact (pow_ne_zero 2 h') (tendsto_nhds_unique (f:=fun i:ℕ=> ‖x‖^2) tendsto_const_nhds (by simpa only [he] using hp))
end YM.Signs
