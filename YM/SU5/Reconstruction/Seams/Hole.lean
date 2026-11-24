import YM.SU5.Reconstruction.Seams.Ultralimit
/-! # seam argument pin: limits from real Eu priceable semi-closed plateaus -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice
namespace Sail
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup CF.Floral
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder Classical
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "I"=> Complex.I
local notation "iop"=> (ContinuousLinearMap.id ℂ H)
def phase (p : ℂ) : H.Op := (S.edge (-p.im)).comp (S.E p.re.toNNReal)
lemma width_real (t:ℝ) : phase S (t:ℂ)= S.E t.toNNReal := by unfold phase; simp [S.birth]
lemma width_imaginary (t:ℝ) : phase S (sideways t)= S.edge t:=by unfold phase; simp [sideways,S.eZero]-- names tune
lemma phase_meets {t:ℂ} (p : t∈inside): phase S t = S.F t := by
  unfold phase; rw [← S.roots_heat (show 0<t.re.toNNReal from Real.toNNReal_pos.mpr p),S.along (dur.mpr (Real.toNNReal_pos.mpr p))]
  apply congrArg S.F; apply Complex.ext <;> simp [duration,sideways,(show 0<t.re from p).le]
lemma phase_ana : AnalyticOnNhd ℂ (phase S) inside:= by
  intro t p; apply (S.localHeat t p).congr; exact Eventually.mono (open_inside.mem_nhds p) (fun i q=> (phase_meets S q).symm) -- orientation check
private lemma joint_contAux {α : Type*} {f:Filter α}{F:α→H.Op}{g:α→H} {C:ℝ} (u : 0<C) (v:∀ a,‖F a‖≤ C) (A:H.Op) (h:∀ x:H,Tendsto (fun i=> F i x) f (𝓝 (A x))) {b:H} (e:Tendsto g f (𝓝 b)) : Tendsto (fun i=> F i (g i)) f (𝓝 (A b)):= by
  apply Metric.tendsto_nhds.mpr; intro ε p
  filter_upwards [Metric.tendsto_nhds.mp e (ε/(2*C)) (by positivity),Metric.tendsto_nhds.mp (h b) (ε/2) (by positivity)] with i t k
  have hb : dist (F i (g i)) (F i b) ≤ C * dist (g i) b := by
    rw [dist_eq_norm,←map_sub, dist_eq_norm]; exact ((F i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (v i) (by positivity))
  apply lt_of_le_of_lt (dist_triangle _ (F i b) _); nlinarith [(lt_div_iff₀ (show (0:ℝ)<2*C by positivity)).mp t] -- need k typed
lemma phase_cont (F:ℂ→ℂ)(g:ℂ→H)(hc:Continuous g)(he:Continuous F) : Continuous fun i=> phase S (F i) (g i):=by
  unfold phase; simp_rw [ContinuousLinearMap.comp_apply]; refine S.cont_edge _ _ ?_ ((Complex.continuous_im.comp he).neg); apply continuous_iff_continuousAt.mpr; intro z; exact joint_contAux zero_lt_one (fun i=> S.shrinks (F i).re.toNNReal) _ (fun x=>(S.continuousE x).continuousAt.tendsto.comp ((continuous_real_toNNReal.comp (Complex.continuous_re.comp he)).continuousAt.tendsto)) hc.continuousAt

-- Two formulas with j seam. wp0,w1 widths, r padding external both sides
variable (r:ℝ≥0)(A B:H.Op)(L R:H)
local notation "𝔯"=> ((r:ℝ):ℂ)
local notation "β"=> phase S
local notation "𝒟"=> (S.E r)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
noncomputable def before (A B:H.Op)(L R:H)(i j:ℝ)(z:ℂ) := inner ℂ L (𝒟 (A (phase S (z-i) (B (phase S (𝔯 - j - z) R)))))
noncomputable def after (A B:H.Op)(L R:H)(i j:ℝ)(z:ℂ) := inner ℂ L (phase S (𝔯+z) (B (phase S (-z-j) (A (S.E (ℜ ((r:ℝ)-i)) R)))))
lemma vCont : Continuous (before S r A B L R 0 0):= by
  unfold before; refine continuous_const.inner ((𝒟).continuous.comp (A.continuous.comp (phase_cont S _ _ (B.continuous.comp (phase_cont S _ _ continuous_const (by fun_prop))) (by fun_prop))))
lemma wCont : Continuous (after S r A B L R 0 0):= by
  unfold after; exact continuous_const.inner (phase_cont S _ _ (B.continuous.comp (phase_cont S _ _ continuous_const (by fun_prop))) (by fun_prop))
private lemma tick {v:ℂ→ℂ}{x:ℂ→H} (z:ℂ)(hx : DifferentiableAt ℂ x z)(hv:DifferentiableAt ℂ v z) (p : v z∈inside): DifferentiableAt ℂ (fun i=> phase S (v i) (x i)) z:= by
  exact DifferentiableAt.clm_apply (show DifferentiableAt ℂ (fun i=> phase S (v i)) z from (phase_ana S (v z) p).differentiableAt.comp z hv) hx
lemma before_ana (a : ℝ): AnalyticOnNhd ℂ (before S r A B L R 0 0) (veil 0 r a) := by
  refine DifferentiableOn.analyticOnNhd ?_ (veil_open _ _ _)
  intro t h; apply DifferentiableAt.differentiableWithinAt; unfold before; apply ( (innerSL ℂ L).differentiableAt).comp _ (f:=fun p:ℂ => 𝒟 _)
  apply ((𝒟).differentiableAt).comp _; refine (A.differentiableAt).comp _ (tick S t ((B.differentiableAt).comp _ (tick S _ (differentiableAt_const _) ((differentiableAt_const _).sub differentiableAt_id) ?_)) (differentiableAt_id.sub (differentiableAt_const _)) ?_) -- adjust
  · change 0<(𝔯-(↑(0:ℝ):ℂ)-t).re; simpa using sub_pos.mpr h.2.1
  change 0<(t-(↑(0:ℝ):ℂ)).re; simpa using h.1
lemma after_ana (a:ℝ): AnalyticOnNhd ℂ (after S r A B L R 0 0) (veil (-(r:ℝ)) 0 a) := by
  refine DifferentiableOn.analyticOnNhd ?_ (veil_open _ _ _)
  intro z h; apply DifferentiableAt.differentiableWithinAt
  refine ((innerSL ℂ L).differentiableAt).comp _ (tick S z ((B.differentiableAt).comp _ (tick S z (differentiableAt_const _) (differentiableAt_id.neg.sub (differentiableAt_const _)) ?_)) ((differentiableAt_const _).add differentiableAt_id) ?_)
  · change 0 < (-z-(↑(0:ℝ):ℂ)).re; simpa using h.2.1
  change 0 < (𝔯+z).re; simp; linarith [show -(r:ℝ)< z.re from h.1]

-- real edge & phase resolution

lemma phaseEdge {z:ℂ} (p:z∈inside) (t:ℝ) : phase S (z+sideways t)=(S.edge t).comp (phase S z) := by
  rw [phase_meets S ((allow _ _).mpr p),phase_meets S p,S.along p]
lemma phaseHeld {z:ℂ} (p:z∈inside) (t:ℝ) : phase S (z+sideways t)=(phase S z).comp (S.edge t) := by
  rw [phase_meets S ((allow _ _).mpr p),phase_meets S p,S.either p]
-- remove include

noncomputable def LorTime (t:ℝ) (A:H.Op): H.Op:= (S.edge t).comp (A.comp (S.edge (-t)))
lemma payoff (t:ℝ)(b:0<r) : before S r A B L R 0 0 (sideways t)= inner ℂ (S.E r L) (A (LorTime S t B (S.E r R))) := by
 rw [before,Complex.ofReal_zero,sub_zero,width_imaginary]; rw [show ((r:ℝ):ℂ) -0 - sideways t= 𝔯+sideways (-t) from by simp [sideways]] -- cast maybe gone
 rw [← S.swing,phaseEdge S (dur.mpr b),width_real, Real.toNNReal_coe]; rfl
lemma payoff_after (t:ℝ)(b:0<r): after S r A B L R 0 0 (sideways t)=inner ℂ (S.E r L) (LorTime S t B (A (S.E r R))) := by -- H- negative t? H-(edge at z) = Edge(t) B Edge(-t) A.
  rw [after,phaseHeld S (dur.mpr b), show -sideways t-(↑(0:ℝ):ℂ)=sideways (-t) from (by simp [sideways]),width_imaginary,width_real,sub_zero,Real.toNNReal_coe,ContinuousLinearMap.comp_apply,S.swing]; rfl

/-- Anchor price formulas as used. -/
lemma before_real (c:ℝ)(u v:ℝ) : before S r A B L R u v (c:ℂ)=
    inner ℂ (S.E r L) (A (S.E ((c-u).toNNReal) (B (S.E (((r:ℝ)-v-c).toNNReal) R)))):=by
  rw [before,← Complex.ofReal_sub,← Complex.ofReal_sub,← Complex.ofReal_sub,width_real,width_real,S.swing]
lemma after_real (c:ℝ)(u v:ℝ) : after S r A B L R u v (c:ℂ)=
    inner ℂ (S.E (((r:ℝ)+c).toNNReal) L) (B (S.E ((-c-v).toNNReal) (A (S.E (((r:ℝ)-u).toNNReal) R)))):=by
  rw [after,← Complex.ofReal_neg,← Complex.ofReal_sub,← Complex.ofReal_add,width_real,width_real,S.swing]

structure Anchors (X : ℕ→ H.Op)(a:H.Op): Prop where
 uniform : ∃ M:ℝ,0<M ∧ ∀ i,‖X i‖ ≤ M
 point (v:H): Tendsto (fun i=> X i v) atTop (𝓝 (a v))

lemma Anchors.cont {A:ℕ→H.Op}{a:H.Op} (u:Anchors A a){x:ℕ→ H}{z:H}(e:Tendsto x atTop (𝓝 z)): Tendsto (fun i=> A i (x i)) atTop (𝓝 (a z)):= by
  obtain ⟨c,v,w⟩:= u.uniform; exact joint_contAux v w a u.point e

lemma blurry {t:ℕ→ℝ} {x:ℝ} (p:Tendsto t atTop (𝓝 x)) {y:ℕ→ H} {w:H} (v : Tendsto y atTop (𝓝 w)) : Tendsto (fun i=> S.E (ℜ (t i)) (y i)) atTop (𝓝 (S.E (ℜ x) w)):=joint_contAux zero_lt_one (fun i=> S.shrinks _) _ (fun x=>(S.continuousE x).continuousAt.tendsto.comp (continuous_real_toNNReal.continuousAt.tendsto.comp p)) v

-- pointwise norm convergence with variable price widths shrink to time0; require operator only SOT
lemma settles {U V : ℕ→ H.Op} {u v:ℕ→ℝ} (p:Anchors U A) (q:Anchors V B)(hu:Tendsto u atTop (𝓝 0))(hv:Tendsto v atTop (𝓝 0)) (z:ℝ) :
    Tendsto (fun i=> before S r (U i) (V i) L R (u i) (v i) (z:ℂ)) atTop (𝓝 (before S r A B L R 0 0 z)) ∧
    Tendsto (fun i=> after S r (U i) (V i) L R (u i) (v i) (z:ℂ)) atTop (𝓝 (after S r A B L R 0 0 z)):=by
  simp_rw [before_real,after_real]; constructor
  · exact tendsto_const_nhds.inner (p.cont (blurry S (tendsto_const_nhds.sub hu) (q.cont (blurry S ((tendsto_const_nhds.sub hv).sub tendsto_const_nhds) tendsto_const_nhds))))
  exact tendsto_const_nhds.inner (q.cont (blurry S (tendsto_const_nhds.sub hv) (p.cont (blurry S (tendsto_const_nhds.sub hu) tendsto_const_nhds))))

/-- Seam analytic key. Used after the perpendicular axis is able to afford the slit continuation for those
 real Euclidean data. Then equality in SPACELIKE j-direction for these slice operator matrix elements. -/
theorem seam_bill {U V : ℕ→ H.Op} {u v:ℕ→ℝ} (p:Anchors U A) (q:Anchors V B) (hu:Tendsto u atTop (𝓝 0))(hv:Tendsto v atTop (𝓝 0))(w:0<r)
    {a:ℝ} (b:0<a) {F:ℕ→ℂ→ℂ} {D:Set ℝ} (d:Dense D) (H₁:∀ n, Hol (slit a) (F n)) (H₂:∃ c:ℝ,∀ n,∀ z∈slit a, ‖F n z‖≤ c)
    (cp:∀ x∈ Ioo 0 (r:ℝ),x∈D→∀ᶠ n in atTop,before S r (U n) (V n) L R (u n) (v n) (x:ℂ)=F n x)
    (cn:∀ x∈ Ioo (-(r:ℝ)) 0,x∈D→∀ᶠ n in atTop,after S r (U n) (V n) L R (u n) (v n) (x:ℂ)=F n x)
    (t:ℝ)(tz: |t|<a) : inner ℂ (S.E r L) (A (LorTime S t B (S.E r R))) = inner ℂ (S.E r L) (LorTime S t B (A (S.E r R))) := by
  rw [←payoff S r A B L R t w, ←payoff_after S r A B L R t w]; obtain ⟨c,h⟩:=H₂
  exact seam_chance F b w H₁ h D d (before_ana S r A B L R a) (after_ana S r A B L R a)
    (fun x hx w=> ((settles S r A B L R p q hu hv x).1.congr' (cp x hx w)))
    (fun x hx w=> ((settles S r A B L R p q hu hv x).2.congr' (cn x hx w)))
    _ (by simpa [slit,sideways]) (side _) (vCont S r A B L R).continuousAt (wCont S r A B L R).continuousAt
end Sail
end YM.ConePrice
