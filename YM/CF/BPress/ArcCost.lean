import YM.CF.BPress.Chord
import YM.Gauge.Nearest
/-! Local chart and uniform finite-dimensional Taylor tools (Frobenius!)
for the B-method. `law_log` etc. separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress
open Function Filter Lattice Gauge MeasureTheory LocalH
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff NNReal ENNReal Classical
attribute [local instance] frobInner

section
variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
-- on a sufficiently small ball about an arbitrary center. constant choices before everything
lemma taylor_change (x : F) {f : F→K} (h : ContDiffAt ℝ ω f x) {L : F →L[ℝ] K} (t : HasFDerivAt f L x) :
    ∃ a C : ℝ, 0<a ∧ 0<C ∧ ∀ r < a, ∀ v∈Metric.closedBall x r, ∀ u∈Metric.closedBall x r,
    ‖f v - f u - L (v-u)‖ ≤ C*r* ‖v-u‖ := by
  have hc : ContDiffAt ℝ ω (fderiv ℝ f) x:= by
    apply h.fderiv_right <;> simp -- tune
  obtain ⟨C,b,p,P⟩:= (hc.hasStrictFDerivAt (by simp)).exists_lipschitzOnWith
  have hl:= h.eventually (by simp); obtain ⟨r,s,hp⟩:=Metric.mem_nhds_iff.mp (inter_mem p hl); refine ⟨r,C+1,s,by positivity, fun u l v w y hy=>?_⟩
  rw [← t.fderiv]; have he:=Metric.closedBall_subset_ball (x:=x) l; refine le_trans ((convex_closedBall x u).norm_image_sub_le_of_norm_fderiv_le' (fun y hy=>(show ContDiffAt ℝ ω f y from (hp (he hy)).2).differentiableAt (by simp)) (C:=C*u) ?_ hy w) ?_
  · intro i q; have e:= P.dist_le_mul i (hp (he q)).1 x (mem_of_mem_nhds p); rw [dist_eq_norm] at e; exact e.trans (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp q) C.property)
  have g : 0≤u:=dist_nonneg.trans (Metric.mem_closedBall.mp w); gcongr; exact le_add_of_nonneg_right zero_le_one
end
namespace chord
variable {G : Gauge}
abbrev emb (G : Gauge) (x : G.Color) := G.mat (G.lieExp x)
lemma exp_lip (G : Gauge) (R : ℝ) : ∃ K : ℝ≥0, LipschitzOnWith K (emb G) (Metric.closedBall 0 R):= G.exp_jet.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall ..) (isCompact_closedBall ..) -- tune
lemma exp_neg (x : G.Color) : G.lieExp (-x)=(G.lieExp x)⁻¹:= by
  apply G.mat_injective; rw [G.mat_lieExp,G.mat_inv,G.mat_lieExp,NormedSpace.star_exp,G.colorMat_skew,map_neg] -- tune
lemma exp_conj (x : G.Color) (z : G.El) : G.lieExp (G.adjoint z x)=z*G.lieExp x*z⁻¹:= by
  apply G.mat_injective; rw [G.mat_mul,G.mat_mul,G.mat_inv,G.mat_lieExp,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl
-- on a sufficiently small chord ball. resulting log/read and Lie neighborhood
structure Chart (G : Gauge) where
  δ : ℝ
  eps : ℝ
  C : ℝ
  size : 0 < δ
  radius : 0 < eps
  span : 0 < C
  snap_small (x : G.El) : G.chord x ≤ δ → ‖LocalH.snap G x‖<eps
  read (x : G.El) : G.chord x ≤ δ → G.lieExp (LocalH.snap G x)=x
  unroll (x : G.Color) : ‖x‖<eps → LocalH.snap G (G.lieExp x)=x
  fee (x y : G.El) : G.chord x ≤ δ → G.chord y ≤ δ → dist (LocalH.snap G x) (LocalH.snap G y) ≤ C * chord x y
namespace Chart
variable (X : Chart G)
lemma neg (x : G.El) (h : G.chord x ≤ X.δ) : snap G x⁻¹= -(snap G x):=by
  nth_rw 1 [← X.read x h,←exp_neg]; exact X.unroll _ (by rw [norm_neg]; exact X.snap_small x h)
lemma conj (x g : G.El) (h : G.chord x ≤ X.δ) : snap G (g*x*g⁻¹)=G.adjoint g (snap G x):= by
  nth_rw 1 [← X.read x h]; rw [←exp_conj]; exact X.unroll _ (by rw [G.norm_adjoint]; exact X.snap_small x h)
lemma snap_bound (x : G.El) (h : G.chord x ≤ X.δ) : ‖snap G x‖ ≤ X.C * G.chord x:=by simpa [snap] using X.fee x 1 h (G.chord_one ▸ X.size.le)
-- define fallback outside this *open* ball, also measurable at the boundary
-- open ball in eq:B-mood; equality of little role (Mood implies tighter).
def logV (x : G.El) := if G.chord x<X.δ then snap G x else 0
lemma logV_conj (x g : G.El) : X.logV (g*x*g⁻¹)= G.adjoint g (X.logV x):= by
 simp only [logV,G.chord_conj]; split; swap; · simp
 exact X.conj x g (le_of_lt (by assumption))
lemma logV_meas : Measurable X.logV:=by
  let S : Set G.El:= {x| G.chord x< X.δ}; have h : IsOpen S:= isOpen_lt G.continuous_chord continuous_const; apply ContinuousOn.measurable_piecewise (s:=S) (f:=snap G) _ continuousOn_const h.measurableSet; intro x hx
  apply ContinuousAt.continuousWithinAt
  refine Metric.continuousAt_iff'.mpr fun v p=>?_ ; have ht:(fun a=> X.C* chord a x) x=0:=by simp
  have he:= ContinuousAt.tendsto (show ContinuousAt (fun a=> X.C * chord a x) x from continuous_const.continuousAt.mul ((chord.cont (G:=G)).comp (continuous_id.prodMk continuous_const)).continuousAt); rw [chord.refl,mul_zero] at he; filter_upwards [he.eventually (gt_mem_nhds p), h.mem_nhds hx] with a j l; exact (X.fee a x (show _<_ from (show G.chord a<X.δ from l)).le (show G.chord x<X.δ from hx).le).trans_lt j
end Chart
lemma chart (G : Gauge) : Nonempty (Chart G):=by
  obtain ⟨r,h,R⟩:= Metric.mem_nhds_iff.mp G.plog_left
  let g:G.El→G.Color:=snap G
  obtain ⟨K,A,p,t⟩:= (G.plog_diff.hasStrictFDerivAt (by simp)).exists_lipschitzOnWith
  have hx : Tendsto g (𝓝 1) (𝓝 0):=by
    have he := G.plog_diff.continuousAt.tendsto; rw [G.plog_one] at he; exact he.comp (G.continuous_mat.tendsto _)
  obtain ⟨d,e,b⟩:= to_ball (G:=G) (S:={x:G.El| emb G (g x)=G.mat x ∧ g x∈ Metric.ball 0 r ∧ G.mat x∈A}) (by
    filter_upwards [G.plog_right, hx (Metric.ball_mem_nhds _ h), G.continuous_mat.continuousAt.preimage_mem_nhds (x:=1) p] with x H v u; exact ⟨congrArg G.mat H,v,u⟩)
  refine ⟨⟨d,r,K*G.colorScale+1,e,h,by have he:= G.colorScale_pos; positivity,fun x v=>?_,fun x v=>G.mat_injective (b (show x∈G.shell d from v)).1, fun x p=> R (show x∈Metric.ball 0 r by simpa using p),?_ ⟩⟩
  · simpa using Metric.mem_ball.mp (b (show x∈G.shell d from v)).2.1
  intro x y hx hy; apply le_trans (t.dist_le_mul (G.mat x) (b (show x∈G.shell d from hx)).2.2 (G.mat y) (b (show y∈G.shell d from hy)).2.2)
  rw [dist_eq_norm,←scale_mul,←mul_assoc]; gcongr; exact positive ..
  exact le_add_of_nonneg_right zero_le_one
end chord
end YM.CF.BPress
