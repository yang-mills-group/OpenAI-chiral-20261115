import YM.CF.BPress.ArcCost
import YM.CF.BPress.Grid.Coarse
/-!
Dyadic interpolation step of lem:B-frames, using ambient arithmetic mean projected to SU.
Implement as tensor grid refinement (successive midpoint means in the axes; within the choice of
algorithms in the lemma, maintaining the same dyadic bound). Controlled even without a Lipschitz
price on the selector by controlling deviation of each of the projected means. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
namespace Half
open Function Metric Filter Lattice MeasureTheory Finset SU Gauge Cube
open scoped Topology BigOperators ContDiff NNReal InnerProductSpace Matrix Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}
def half : ℝ:=2⁻¹
def mean (u v:G.El) : G.Mat:= half • (G.mat u+G.mat v)
lemma mean_right (u v w:G.El): mean (u*w) (v*w)=mean u v *G.mat w:=by rw [mean,mean,G.mat_mul,G.mat_mul,← add_mul,Algebra.smul_mul_assoc]
lemma mean_left (u v w:G.El): mean (w*u) (w*v)=G.mat w * mean u v:=by rw [mean,mean,G.mat_mul,G.mat_mul,← mul_add,Algebra.mul_smul_comm]
lemma mean_comm (u v:G.El): mean u v=mean v u:= by rw [mean,mean,add_comm]
lemma half_pos : 0<half:= by norm_num [half]
lemma mean_same (u : G.El): mean u u=G.mat u:=by rw [mean,← two_smul ℝ]; exact inv_smul_smul₀ (show (2:ℝ)≠0 by norm_num) _
lemma mean_pair (u v w x:G.El) : ‖mean u w-mean v x‖ ≤ half*(‖G.mat u-G.mat v‖+‖G.mat w-G.mat x‖) := by
 rw [mean,mean,←smul_sub, norm_smul,Real.norm_of_nonneg Half.half_pos.le, add_sub_add_comm]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) Half.half_pos.le
lemma half_price (u v : G.El) : ‖mean u v-G.mat u‖=half*‖G.mat v-G.mat u‖:=by
 conv_lhs=> arg 1; rhs; rw [← mean_same u]
 rw [mean,mean,←smul_sub,add_sub_add_left_eq_sub,norm_smul,Real.norm_of_nonneg Half.half_pos.le]
-- quadratic estimate via taylor at tangent. First work around identity by multiplying mean to identity coordinates. uniform around ALL points. not needing measurable nearest on entire neighborhood of measure zero.
theorem mean_taylor (G:Gauge): ∃ δ K : ℝ, 0<δ ∧ 0<K ∧ ∀ a < δ, ∀ x y : G.El, chord x y ≤ a → ∀ u, G.Nearest u (mean x y)→ ‖G.mat u-mean x y‖≤ G.colorScale*(K*a^2) := by
  let P : G.Mat→ G.Mat:=fun x=> G.mat (G.focus x); obtain ⟨d,K,h,p,t⟩:= taylor_change _ G.focus_diff G.focus_deriv.hasFDerivAt
  obtain ⟨r,f,R⟩:=Metric.mem_nhds_iff.mp G.nearest_is_focus; let κ:=G.colorScale; have hK:0<κ:=G.colorScale_pos
  have F (u:G.El) : G.Nearest u (G.mat u):=fun _=>by rw [sub_self,norm_zero]; positivity
  have hP (x:G.El)(p:‖G.mat x-1‖<r): P (G.mat x)=G.mat x:= by
    have hx: G.mat x∈ball (1:G.Mat) r:= mem_ball.mpr (dist_eq_norm ..|>.trans_lt p); exact congrArg G.mat (R hx x (F x)).symm
  have hc: ∀ (a:ℝ), a < (min r d)/κ → ∀ y u:G.El, chord 1 y ≤ a → G.Nearest u (mean 1 y)→ ‖G.mat u- mean 1 y‖≤ G.colorScale*(2*K*κ*a^2):=by
    intro a k y u v g; let b:=κ*a; let X:= mean 1 y; let Y:=G.mat y; have hz: ‖Y-1‖≤ b:=by rw [norm_sub_rev]; exact (chord.scale_mul 1 y).symm |>.le.trans (mul_le_mul_of_nonneg_left v hK.le) -- tune impossible cast
    have hb: b<d:= lt_of_lt_of_le (by rw [lt_div_iff₀ hK,mul_comm] at k; exact k) (min_le_right r d); have hl:b <r:= lt_of_lt_of_le (by rw [lt_div_iff₀ hK,mul_comm] at k; exact k) (min_le_left r d)
    have hy : X-1= half • (Y-1):= by
      change mean 1 y-1=_; calc
        _ = mean 1 y- mean (1:G.El) 1 := by rw [mean_same,G.mat_one]
        _ = _:= by unfold mean; rw [←smul_sub,add_sub_add_left_eq_sub,G.mat_one]
    let T:= G.lie.starProjection; have q:‖X-1‖ ≤ b:= by rw [hy,norm_smul,Real.norm_of_nonneg Half.half_pos.le]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [half])).trans hz
    have hw:= R (mem_ball.mpr (dist_eq_norm X 1|>.trans_lt (q.trans_lt hl))) u g; have pos:= (norm_nonneg _).trans hz; have h1:P 1=1:= hP 1 (by simpa using f)
    have hj (z:G.Mat)(h:‖z-1‖ ≤ b): ‖P z-P 1-T (z-1)‖≤ K*b*b:=(t _ hb z (mem_closedBall.mpr ((dist_eq_norm ..).le.trans h)) _ (mem_closedBall_self pos)).trans (mul_le_mul_of_nonneg_left h (mul_nonneg p.le pos))
    have hk := hj _ q; have hg:= hj _ hz; rw [hw]; change ‖P X-X‖≤_
    rw [show P X-X= (P X-P 1-T (X-1)) - half • (P Y-P 1-T (Y-1)) by rw [h1,hP y (hz.trans_lt hl), hy,map_smul, smul_sub,← hy]; abel]; apply (norm_sub_le ..).trans; rw [norm_smul,Real.norm_of_nonneg Half.half_pos.le]; apply (add_le_add hk ((mul_le_of_le_one_left (norm_nonneg _) (by norm_num [half])).trans hg)).trans_eq; change _= κ*_; unfold b; ring
  refine ⟨min r d/κ,2*K*κ, div_pos (lt_min f h) hK,by positivity,fun a p x y v u g=>?_⟩; have he:= (Gauge.nearest_left G x⁻¹ _ _).mpr g; rw [← mean_left, inv_mul_cancel] at he; apply (hc a p (x⁻¹*y) _ (by rwa [← chord.left (w:=x⁻¹), inv_mul_cancel] at v) he)|>.trans'; rw [← inv_mul_cancel x,mean_left,G.mat_mul,← mul_sub,mul_frob_eq _ _ (G.mat_star_mul _)]

-- use only SU case (Borel space already installed in FiniteGaugeData)
structure Method where
  pick : E×E→ E
  chosen (x y) : group.Nearest (pick (x,y)) (mean x y)
  borel : Measurable pick
private lemma closed (G:Gauge): IsClosed {x:(G.El × G.El)× G.El|G.Nearest x.2 (mean x.1.1 x.1.2)} := by
  let A := {x:(G.El × G.El)× G.El|G.Nearest x.2 (mean x.1.1 x.1.2)}
  have he : Continuous (fun x:G.El × G.El=>mean x.1 x.2):=(continuous_const (y:=half)).smul ((G.continuous_mat.comp continuous_fst).add (G.continuous_mat.comp continuous_snd))
  have ht : Continuous (fun x:(G.El × G.El)× G.El=>mean x.1.1 x.1.2):=he.comp continuous_fst
  have hA:IsClosed A:=by
    unfold A Nearest; simp_rw [Set.setOf_forall]; exact isClosed_iInter fun i=> isClosed_le (ht.sub (G.continuous_mat.comp continuous_snd)|>.norm) ((ht.sub continuous_const).norm)
  exact hA
private lemma selector (G:Gauge) : ∃ T : G.El × G.El → G.El, Measurable T ∧ ∀ x : G.El×G.El, G.Nearest (T x) (mean x.1 x.2) := by
  letI : TopologicalSpace.MetrizableSpace G.Mat:= inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin G.repDim → Fin G.repDim → ℂ)); letI : TopologicalSpace.MetrizableSpace G.El:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.metrizableSpace
  let A := {x:(G.El × G.El)× G.El|G.Nearest x.2 (mean x.1.1 x.1.2)}
  obtain ⟨P,p,H⟩:=closed_selector A (closed G) (fun x : G.El×G.El=> G.nearest_exists (mean x.1 x.2))
  exact ⟨P,p,H⟩
lemma provides : Nonempty Method := by
 obtain ⟨T,t,g⟩:=selector SU.group; exact ⟨⟨T,fun i j=>g (i,j),t⟩⟩
-- convert midpoint estimates; including a parallel transport by U. 
structure Price (δ K:ℝ):Prop where
 positive : 0<K
 room : 0<δ
 moment (P:Method)(x y:E)(a:ℝ): a<δ→ chord x y≤a→ ‖group.mat (P.pick (x,y))- mean x y‖≤ group.colorScale*(K*a^2)
namespace Price
variable {δ K a:ℝ}{P:Method} (h:Price δ K)
include h
lemma spanL (X Y:E) (p:a<δ) (g:chord X Y≤a) : chord (P.pick (X,Y)) X ≤ a/2 + K*a^2 ∧ chord (P.pick (X,Y)) Y ≤ a/2+K*a^2:=by
 let k:= group.colorScale; have he:=h.moment P X Y a p g; let f:=P.pick (X,Y); have hf (V W:E)(p:mean X Y=mean V W)(g:chord V W≤a): chord f V ≤ a/2+K*a^2:=by
    apply le_of_mul_le_mul_left _ (group.colorScale_pos); rw [chord.scale_mul]; rw [p] at he; apply (norm_sub_le_norm_sub_add_norm_sub _ (mean V W) _).trans; rw [half_price,←chord.scale_mul, chord.comm W V]; refine (add_le_add he (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left g group.colorScale_pos.le) Half.half_pos.le)).trans_eq ?_; unfold half; ring
 exact ⟨hf X Y rfl g, hf Y X (mean_comm ..) ((chord.comm ..).le.trans g)⟩
lemma spanM (X Y V W U:E) (p:a<δ)(g:chord X Y≤a)(q:chord V W≤a)(t:ℝ)(x:chord (X*U) V≤t)(y:chord (Y*U) W≤t):
    chord (P.pick (X,Y)*U) (P.pick (V,W))≤ t+ 2*K*a^2:=by
 let k:= group.colorScale; let A:=P.pick (X,Y); let B:=P.pick (V,W); apply le_of_mul_le_mul_left _ group.colorScale_pos; rw [chord.scale_mul]; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (mean (X*U) (Y*U)) _); refine (add_le_add (b:= group.colorScale*(K*a^2)) ?_ ((norm_sub_le_norm_sub_add_norm_sub _ (mean V W) _).trans (add_le_add (b:= half*(k*t+k*t)) ?_ ((norm_sub_rev ..).le.trans (h.moment P V W a p q))))).trans_eq ?_ -- tune
 · rw [mean_right X Y U,group.mat_mul,←sub_mul,frob_mul_eq _ _ (group.mat_mul_star _)]; exact h.moment P X Y a p g
 · refine (mean_pair (X*U) V (Y*U) W).trans ?_; rw [← chord.scale_mul, ← chord.scale_mul]; exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left x group.colorScale_pos.le) (mul_le_mul_of_nonneg_left y group.colorScale_pos.le)) Half.half_pos.le
 unfold k half; ring
end Price
end Half
end YM.CF.BPress.Grid
