import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
-- tools for the comparator Jet prices
set_option autoImplicit false
noncomputable section
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology NNReal ENNReal
namespace YM.CF.Floral
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]{f:ℂ→E}{D:Set ℂ}{c:ℂ}{r C:ℝ}
abbrev Hol (D:Set ℂ)(f:ℂ→E) := DifferentiableOn ℂ f D
lemma c_deriv (hf:Hol D f)(hr:0<r)(hd:closedBall c r⊆D)(h:∀ x∈D, ‖f x‖≤C) : ‖deriv f c‖≤C/r:=
 norm_deriv_le_of_forall_mem_sphere_norm_le hr ⟨hf.mono (ball_subset_closedBall.trans hd), hf.continuousOn.mono ((closure_minimal ball_subset_closedBall isClosed_closedBall).trans hd)⟩ (fun _ g=> h _ (hd (sphere_subset_closedBall g)))
variable [CompleteSpace E] {ι:Type*}{F:ι→ℂ→E}{l:Filter ι}[l.NeBot]
-- pointwise convergence, using Cauchy estimates
lemma chalk (d:IsOpen D)(hF:∀ᶠ i in l,Hol D (F i))(hv:∀ᶠ i in l,∀ x∈D,‖F i x‖≤C)(p:∀ x∈D,Tendsto (fun i=> F i x) l (𝓝 (f x))): Hol D f:=by
 suffices TendstoLocallyUniformlyOn F f l D from this.differentiableOn hF d
 rw [Metric.tendstoLocallyUniformlyOn_iff]; intro ε he x hx
 obtain ⟨r,hr,H⟩:= nhds_basis_closedBall.mem_iff.mp (d.mem_nhds hx); let K:=ball x (r/2); let c:=C/(r/2)
 have hs(y)(g:y∈K): closedBall y (r/2) ⊆ D:=by
    intro z hz; apply H; rw [mem_closedBall]; have hg:=dist_triangle z y x; have hb:=mem_closedBall.mp hz; have ha:=mem_ball.mp g; linarith
 have hD:K⊆D:=fun y g=> hs y g (mem_closedBall_self (by linarith))
 have hk:x∈K:=mem_ball_self (half_pos hr)
 have ht:∀ᶠ i in l,∀ y∈K,dist (F i y) (F i x)≤ c*dist y x:=by
    filter_upwards [hF,hv] with i hh hB y g; rw [dist_eq_norm,dist_eq_norm]; exact (convex_ball x (r/2)).norm_image_sub_le_of_norm_deriv_le (fun y g=> hh.differentiableAt (d.mem_nhds (hD g))) (fun y g=> c_deriv hh (half_pos hr) (hs y g) hB) hk g
 have hL(y)(g:y∈K):dist (f y) (f x)≤ c*dist y x:= le_of_tendsto ((p y (hD g)).dist (p x hx)) (ht.mono fun i v=> v _ g)
 let T:={y | c*dist y x<ε/3}
 have hP:0<ε/3:=by positivity
 refine ⟨K∩T,mem_nhdsWithin_of_mem_nhds (inter_mem (ball_mem_nhds x (by linarith)) ((isOpen_lt (f:=fun y=>c*dist y x) (by fun_prop) continuous_const).mem_nhds (show x∈T from (by unfold T; simpa)))),?_⟩
 filter_upwards [ht, (p x hx).eventually (ball_mem_nhds (f x) hP)] with i g q y hy
 have hb:= dist_triangle (f y) (f x) (F i y)
 have hg:= dist_triangle (f x) (F i x) (F i y)
 rw [dist_comm _ (F i x),dist_comm (F i x) (F i y)] at hg
 have ha:=g _ hy.1; have hM:=hL _ hy.1; have hv:=mem_ball.mp q; have hw:c*dist y x < ε/3:= hy.2; linarith
end YM.CF.Floral
