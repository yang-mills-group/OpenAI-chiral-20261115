import YM.CF.Vp929.Contour.Accounts
import YM.CF.Vp929.Analysis.Shooting
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Py.Rate
open scoped NNReal
open Complex Function Metric Set Filter Topology
variable {R X:Type*}{x z:ℂ}{t r w Q:ℝ}
-- scalar bound on ball at step k. radius unit l∞ jet formula.Cauchy
lemma pay_deriv (G:ℂ→ℂ)(L:DifferentiableOn ℂ G (ball 0 r))(s:∀ z∈ ball (0:ℂ) r, ‖G z‖≤ Q)(u:z∈ ball (0:ℂ) t)(v:0<w)(e:t+w≤r): ‖deriv G z‖ ≤ Q/w:=by
 have hx: closedBall z w ⊆ ball (0:ℂ) r:= fun x p=> mem_ball.mpr (lt_of_le_of_lt (dist_triangle x z 0) ((add_lt_add_of_le_of_lt (mem_closedBall.mp p) (mem_ball.mp u)).trans_le ((add_comm w t).trans_le e)))
 rw [← Complex.cderiv_eq_deriv isOpen_ball L v hx]; exact Complex.norm_cderiv_le v fun x h=> s _ (hx (sphere_subset_closedBall h))
lemma pay_diff {G:ℂ→ℂ}(L:DifferentiableOn ℂ G (ball 0 r))(s:∀ z∈ ball (0:ℂ) r, ‖G z‖ ≤ Q)(u:z∈ball (0:ℂ) t)(p:x∈ball (0:ℂ) t)(v:0<w)(e:t+w≤r): ‖G x-G z‖ ≤ Q/w * ‖x-z‖:= by
 let t₀:ℝ≥0:= ⟨Q/w, div_nonneg ((norm_nonneg _).trans (s _ (ball_subset_ball (by linarith:t ≤ r) p))) v.le⟩; rw [←dist_eq_norm,←dist_eq_norm]; have H:LipschitzOnWith t₀ G (ball 0 t):= (convex_ball (0:ℂ) t).lipschitzOnWith_of_nnnorm_deriv_le (fun x hx=> L.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith:t≤r) hx))) (fun z hz=> NNReal.coe_le_coe.mp (pay_deriv G L s hz v e)); exact H.dist_le_mul _ p _ u
variable [Sub X]{f:ℂ→Pair X}{c:Book X}{h:Looks X}
lemma Portfolio.gradient (P:Portfolio c h)(hc:h (ball 0 r) f)(g:∀ z∈ball (0:ℂ) r, Both (fun k=> c k Q) (f z))(k: Both (Enough c) (f x-f z))(hx:x∈ ball (0:ℂ) t)(hz:z∈ball (0:ℂ) t)(u:t+w≤r)(v:0<w): Both (fun k=>c k (2*Q/w * ‖x-z‖)) (f x - f z):= by
 let p:Valid c h (ball 0 r) f:= ⟨isOpen_ball,hc,Q,g⟩; let tx:x∈ ball (0:ℂ) r:= ball_subset_ball (by linarith:t≤r) hx; let tz:z∈ball (0:ℂ) r:= ball_subset_ball (by linarith:t≤r) hz
 refine P.evaluate k _ fun F u' s=> ?_; let g':=probing F ∘ f; let i:Accountable c h F:=u'
 rw [show probing F (f x-f z)= g' x-g' z from ?_]; exact pay_diff (i.liable _ _ p) (fun x hx=> Accountable.norm_le P s (g x hx)) hz hx v u
 apply Complex.ext <;> simp only [prob_re,prob_im,sub_re,sub_im,g',comp_apply,Prod.snd_sub,Prod.fst_sub]; exact i.receipt _ _ (p.minted tx).1 (p.minted tz).1 ; exact i.receipt _ _ (p.minted tx).2 (p.minted tz).2
end YM.CF.Py.Rate
