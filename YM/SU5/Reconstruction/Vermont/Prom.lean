import YM.SU5.Reconstruction.Vermont.Spectacle
/-!
# Plan from Eu chart on real data.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup CF.Floral ConePrice Sail ContinuousLinearMap Anvil
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a) (A L:H.Op){T':ℕ→H.Op} (r e:ℝ≥0)(η:ℝ) (p q:H)
variable {f :ℕ→ℂ→ℂ}(p0 : ∀ n, Hol (slit η) (f n))(h:0<η) (p1: ∃ Q :ℝ,∀ n,∀ z∈slit η, ‖f n z‖ ≤ Q)
include h p0 p1
variable (D:Set ℝ)(d:Dense D)
omit p0 p1 in
include d in
private lemma sale (s t:ℝ)(F:ℂ→ ℂ)(W:AnalyticOnNhd ℂ F (slit η)) {G:ℝ→ℂ}(v:Continuous G)
 (p:∀ x∈ D, x∈ Ioo s t→ F (x:ℂ)=G x) (x:ℝ)(u:x∈ Ioo s t) : F x=G x:= by
 exact EqOn.closure (s:= Ioo s t ∩ D) (show EqOn (fun x:ℝ=> F x) G _ from fun z ⟨x,y⟩=>p z y x) (W.continuousOn.comp_continuous Complex.continuous_ofReal (fun _=> slit_ground η h _)) v (show x∈_ from d.open_subset_closure_inter isOpen_Ioo u) -- maybe arg order
variable {v:ℕ→ℝ}(v0:Tendsto v atTop (𝓝 0))(u:Limited atTop T' L)
omit h p0 p1 in
-- oriented sublemma for WOT.
include u in
private lemma limFuel (x:H) {y:ℕ→H}{w:H}(h:Tendsto y atTop (𝓝 w)) : Tendsto (fun i=>inner ℂ x (T' i (y i))) atTop (𝓝 (inner ℂ x (L w))):=by
   obtain ⟨M,q,e⟩:= u.uniform
   have g:Tendsto (fun i=> ‖x‖*(M*‖y i-w‖)+ dist (inner ℂ x (T' i w)) (inner ℂ x (L w))) atTop (𝓝 0):= by simpa using ((((h.sub (tendsto_const_nhds (x:=w))).norm.const_mul M).const_mul ‖x‖).add ((u.confirms x w).dist (tendsto_const_nhds (x:=inner ℂ x (L w)))))
   apply Metric.tendsto_nhds.mpr; intro ε hv; filter_upwards [g.eventually (gt_mem_nhds hv),e] with i hk t
   apply lt_of_le_of_lt (le_trans (dist_triangle _ (inner ℂ x (T' i w)) _) (add_le_add_left ?_ _)) hk
   rw [dist_eq_norm,← inner_sub_right,← map_sub]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((T' i).le_opNorm _).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _))) (norm_nonneg _))
include u v0 d
lemma promotion
    (hv:∀ (w:ℝ), w∈D → w∈ Ioo (e:ℝ) (r:ℝ) → ∀ᶠ n in atTop,before S r A (T' n) p q (e:ℝ) (v n) w=f n w)
    (hu:∀ (w:ℝ), w∈D → w∈ Ioo (-(r:ℝ)) 0→∀ᶠ n in atTop, after S r A (T' n) p q (e:ℝ) (v n) w=f n w):∃ f,Plan S A L r e η p q f:= by
 obtain ⟨Γ,e0⟩:= p1; -- tune: obtain Γ e0 because ∀ n...; cannot ⟨_,_,_⟩
 obtain ⟨F,g,b⟩:=limit_chance f (slit_open _) p0 e0
 let E(x:ℝ):= S.E x.toNNReal; let C (x:ℝ):= after S r A L p q e 0 x; let B (x:ℝ):= before S r A L p q e 0 x
 -- easier use phase_cont then restrict.C for η.
 have hC:Continuous C:= by
   let K:= after S r A L p q e 0; apply (show Continuous K from ?_).comp Complex.continuous_ofReal; unfold K after; exact continuous_const.inner (phase_cont S _ _ (L.continuous.comp (phase_cont S _ _ continuous_const (by fun_prop))) (by fun_prop))
 have hB:Continuous B:=by
   let K:= before S r A L p q e 0; apply (show Continuous K from ?_).comp Complex.continuous_ofReal; unfold K before; exact continuous_const.inner ((S.E r).continuous.comp (A.continuous.comp (phase_cont S _ _ (L.continuous.comp (phase_cont S _ _ continuous_const (by fun_prop))) (by fun_prop))))
 let y := A (S.E (Real.toNNReal ((r:ℝ)-e)) q)
 refine ⟨F,g.mono veil_slit, (fun t h'=> sale _ h _ d _ _ F g hB ?_ t h'),fun t h'=> sale _ h _ d _ _ F g hC ?_ t h'⟩ -- order of include
 · intro x e' t'; apply tendsto_nhds_unique (b (x:ℂ) (slit_ground η h x)); apply Tendsto.mono_left _ (Ultrafilter.of_le atTop); apply Tendsto.congr' (hv x e' t'); unfold B; simp_rw [before_real,← adjoint_inner_left A,← adjoint_inner_left (S.E _)] -- need move E after A
   apply limFuel _ u
   apply Sail.blurry _ _ _; swap; exact tendsto_const_nhds; exact ((tendsto_const_nhds.sub v0).sub tendsto_const_nhds)
 intro x e' t'; apply tendsto_nhds_unique (b (x:ℂ) (slit_ground η h x)); apply Tendsto.mono_left _ (Ultrafilter.of_le atTop); apply Tendsto.congr' (hu x e' t'); unfold C; simp_rw [after_real]; apply limFuel _ u
 exact blurry S (tendsto_const_nhds.sub v0) tendsto_const_nhds
end YM.Lens
