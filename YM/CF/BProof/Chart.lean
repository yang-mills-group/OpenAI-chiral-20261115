import YM.CF.BProof.Chord
import YM.CF.BProof.Taylor

/-! Group chart costs (keep generic). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof
open Filter Metric NormedSpace Function Set MeasureTheory
open scoped Matrix.Norms.Frobenius Topology ContDiff
variable {G : Gauge}
def logG (G : Gauge) (x : G.El) := G.plog (G.mat x)
@[simp] lemma log_one (G : Gauge) : logG G 1=0 := by simp [logG]
lemma map_conj (u : G.El) (v : G.Color) : G.lieExp (G.adjoint u v)=u*G.lieExp v*u⁻¹ := by apply G.mat_injective; simp [G.exp_conjugate]; rfl

/-- `radius` for logs (membership by chord), `size` for linear algebra arguments. -/
structure Chart (G : Gauge) where
 radius : ℝ
 size : ℝ
 C : ℝ
 positive : 0<radius
 admitted : 0<size
 C_one : 1 ≤ C
 exposes (v : G.El) : G.chord v≤ radius → ‖logG G v‖≤ size ∧ G.lieExp (logG G v)=v
 recognizes (v : G.Color) : ‖v‖≤size → logG G (G.lieExp v)=v
 lip (x y : G.El) : G.chord x ≤ radius → G.chord y ≤ radius → ‖logG G x-logG G y‖≤ C*cd G x y
 cost (x y : G.Color) : ‖x‖ ≤ size → ‖y‖≤size → cd G (G.lieExp x) (G.lieExp y) ≤ C*‖x-y‖
 error {r : ℝ} (x y : G.Color) : r≤size → ‖x‖ ≤ r → ‖y‖ ≤ r →
       ‖G.mat (G.lieExp x)-G.mat (G.lieExp y)-G.colorMat (x-y)‖ ≤ C*r*‖x-y‖
 visible : ContinuousOn (logG G) (G.shell radius)

set_option maxHeartbeats 400000 in
lemma chart_bought (G : Gauge) (c : ℝ) (hc : 0<c) : ∃ K : Chart G,K.size ≤ c := by
 obtain ⟨C,d,hC,hd,H⟩:= chargedLip (a:=(0:G.Color)) G.exp_jet.contDiffAt
 obtain ⟨C',d',hC',hd',H'⟩:= quadratic (a:=(0:G.Color)) G.exp_jet.contDiffAt
 obtain ⟨L,v,hL,hv,X⟩:= chargedLip (a:=(1:G.Mat)) G.plog_diff
 have he := G.plog_diff.eventually (by simp) -- args tune
 obtain ⟨r,hr,J⟩:= Metric.mem_nhds_iff.mp G.plog_left
 let u:= min (min c (r/2)) (min d d'); have hu : 0<u:= lt_min (lt_min hc (by positivity)) (lt_min hd hd')
 have hj : u ≤ d := (min_le_right ..).trans (min_le_left ..)
 have hj' : u ≤ d' := (min_le_right ..).trans (min_le_right ..)
 have hr' : u < r := lt_of_le_of_lt ((min_le_left ..).trans (min_le_right ..) : u≤ r/2) (by linarith)
 let W := {x : G.El| ‖logG G x‖≤ u ∧ G.lieExp (logG G x) = x ∧ G.mat x∈closedBall 1 v ∧ ContinuousAt (logG G) x}
 have hn : ContinuousAt (logG G) 1 := (show ContinuousAt G.plog (G.mat 1) from G.plog_diff.continuousAt).comp G.continuous_mat.continuousAt
 have hE : Tendsto G.mat (𝓝 1) (𝓝 1):= G.continuous_mat.tendsto _
 have hw : W∈𝓝 1:=by
   have hy:Tendsto (logG G) (𝓝 1) (𝓝 0):=by rwa [← log_one G]
   filter_upwards [hy.eventually (closedBall_mem_nhds _ hu),G.plog_right,hE.eventually he,hE.eventually (closedBall_mem_nhds _ hv)] with x hx hk hh hl
   exact ⟨show ‖logG G x‖ ≤ u by simpa only [← dist_zero_right] using hx,hk,hl,(show ContDiffAt ℝ ω G.plog (G.mat x) from hh).continuousAt.comp G.continuous_mat.continuousAt⟩ -- tune
 obtain ⟨q,hq,hk⟩:= cd_open (p:=fun x : G.El => x∈ W) G 1 hw
 have hm (x : G.El) (hx : G.chord x ≤ q) : x ∈ W:= hk x (by simpa)
 let o:=G.colorScale; let k:= max 1 (max C' (max (C/o) (L*o)))
 have ho:0<o:= G.colorScale_pos
 have hV:= show max C' (max (C/o) (L*o))≤ k from le_max_right ..
 have hV':= show max (C/o) (L*o) ≤ k from (le_max_right ..).trans hV
 refine ⟨⟨q,u,k,hq,hu,le_max_left ..,fun x h=> ⟨(hm x h).1,(hm x h).2.1⟩,fun x h=> J ?_,fun x y hx hy=>?_,fun x y hx hy=>?_,fun {r'} x y hh hx hy=>?_,fun x hx=> ?_⟩,(min_le_left ..).trans (min_le_left ..)⟩
 · rw [mem_ball,dist_zero_right]; exact h.trans_lt hr'
 · refine le_trans (X _ (hm x hx).2.2.1 _ (hm y hy).2.2.1) ?_
   rw [← dist_eq_norm,mat_norm_dist]; have he : L*o≤k:= (le_max_right ..).trans hV'; linarith only [mul_le_mul_of_nonneg_right he (cd_nonneg G x y)]
 · have hp (x : G.Color)(h : ‖x‖≤u) : x∈closedBall 0 d := mem_closedBall.mpr (by rw [dist_zero_right]; exact h.trans hj)
   rw [cd_norm]; refine (div_le_div_of_nonneg_right (H x (hp x hx) y (hp y hy)) ho.le).trans ?_ -- cd from matrix
   rw [mul_comm C,mul_div_assoc,mul_comm]; exact mul_le_mul_of_nonneg_right ((le_max_left ..).trans hV') (norm_nonneg _)
 · have he : C' ≤ k:= (le_max_left ..).trans hV
   have H := H' r' (hh.trans hj') x (by simpa) y (by simpa)
   erw [G.expDiff_zero.fderiv] at H; exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he ((norm_nonneg x).trans hx)) (norm_nonneg _))
 exact (hm _ hx).2.2.2.continuousWithinAt
namespace Chart
variable (K : Chart G)
lemma width (x : G.El) (h : G.chord x ≤ K.radius) : ‖logG G x‖ ≤ K.C*G.chord x := by simpa [norm_neg, cd_one] using K.lip 1 x (by simpa using K.positive.le) h
lemma step (x : G.Color) (h : ‖x‖≤K.size) : G.chord (G.lieExp x) ≤ K.C*‖x‖:= by simpa using K.cost 0 x (by simpa using K.admitted.le) h
lemma conjugate (u v : G.El) (h : G.chord v ≤ K.radius) : logG G (u*v*u⁻¹)=G.adjoint u (logG G v):=by
 rw [← (K.recognizes (G.adjoint u (logG G v)) (by rw [Gauge.norm_adjoint]; exact (K.exposes _ h).1)),map_conj,(K.exposes _ h).2] -- tune
end Chart
end YM.CF.BProof
