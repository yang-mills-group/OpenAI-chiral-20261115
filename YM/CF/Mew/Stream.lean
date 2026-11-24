import YM.CF.Mew.Hill
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff BigOperators Matrix
variable {I E A :Type*}[Fintype I][DecidableEq I][MeasurableSpace A][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
-- derivative envelope via smaller contour arcs. no ambient extension common
lemma windInt (μ:Measure A)(F:ℂ→A→E)(hp:∀ i:A, DiffContOnCl ℂ (fun z=>F z i) rim) {v:A→ℝ}(hv:Integrable v μ)(hm:∀ z∈rim, AEStronglyMeasurable (F z) μ)(ht:∀ z∈rim,∀ i,‖F z i‖ ≤ v i) (x:ℂ)(u:x∈rim): Integrable (fun i=> deriv (fun z=>F z i) x) μ ∧ HasDerivAt (fun z=>∫ i,F z i∂μ) (∫ i,deriv (fun z=>F z i) x ∂μ) x:=by
 classical
 let d:=(1-‖x‖)/3; have hu:= mem_ball_zero_iff.mp u; have p: 0<d:= by unfold d; linarith
 have hw(z:ℂ)(hz: z∈ ball x d): closedBall z d⊆rim:=by
    intro y hy; apply mem_ball.mpr; have h': dist z x < d:= hz; have hx:dist y z ≤ d:= hy; have hv:=dist_triangle z x 0; rw [dist_zero_right x] at hv; refine lt_of_le_of_lt (dist_triangle y z 0) ?_; dsimp [d] at *; linarith
 have hg: ball x d ⊆rim:= fun z hz=> hw z hz (mem_closedBall_self p.le)
 let g(y:ℂ)(i:A):=deriv (fun t=>F t i) y
 have he{z:ℂ}(i:A)(hz:z∈rim):HasDerivAt (fun w=>F w i) (g z i) z:=((hp i).differentiableOn z hz|>.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
 have hG:AEStronglyMeasurable (g x) μ:=by
    let G(z:ℂ): A→E:= if z∈rim then fun i=> (z-x)⁻¹ • (F z i-F x i) else 0
    refine aestronglyMeasurable_of_tendsto_ae (f:=G) (𝓝[≠] x) (fun i=>?_ ) (ae_of_all _ fun i:A=>?_)
    · unfold G; split; next h=>exact ((hm i h).sub (hm x u)).const_smul _
      exact aestronglyMeasurable_const
    apply Tendsto.congr' _ (hasDerivAt_iff_tendsto_slope.mp (he i u))
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds u)] with z hz; change _=G _ i; unfold G; rw [if_pos (show z ∈ rim from hz)]; rfl
 have hx(y:ℂ)(hy:y∈ ball x d)(i:A): ‖g y i‖ ≤ v i / d:= Complex.norm_deriv_le_of_forall_mem_sphere_norm_le p ((hp i).mono ((ball_subset_closedBall).trans (hw _ hy))) (fun z hz=> ht _ (hw _ hy (sphere_subset_closedBall hz)) _)
 refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) (ball_mem_nhds x p) (Eventually.mono (isOpen_ball.mem_nhds u) (fun i e=>hm _ e)) (hv.mono' (hm _ u) (ae_of_all _ (ht _ u))) hG (Eventually.of_forall fun i y hy=>hx y hy i) (hv.div_const _) (Eventually.of_forall fun i y hy=>he i (hg hy))
lemma riverSum (μ:Measure A)(F: Key I → A → E)(hp:∀ i:A,River (fun j=>F j i)){v:A→ℝ}(hv:Integrable v μ)(hm:∀ z∈hill I, AEStronglyMeasurable (F z) μ)(ht:∀ z∈hill I,∀ i,‖F z i‖ ≤ v i): River (fun z=> ∫ i,F z i∂μ):=by
 refine ⟨continuousOn_of_dominated hm (fun i hi=>ae_of_all _ (ht i hi)) hv (ae_of_all _ fun i=>(hp i).shore),fun x hx i y hy=>?_⟩
 have hz(z:ℂ)(g:z∈rim):update x i z∈hill I:=fill_I hx i (ball_subset_closedBall g)
 exact (windInt μ (fun v=>F (update x i v)) (fun j=>(hp j).circle hx i) hv (fun x hx=>hm _ (hz x hx)) (fun x hx=>ht _ (hz x hx)) _ hy).2.differentiableAt
lemma wind_eq (μ:Measure A)(F: Key I → A → E)(hp:∀ i:A,River (fun j=>F j i)){v:A→ℝ}(hv:Integrable v μ)(hm:∀ z∈hill I, AEStronglyMeasurable (F z) μ)(ht:∀ z∈hill I,∀ i,‖F z i‖ ≤ v i)(x:Key I)(hx:x∈hill I)(i:I): Integrable (fun a=>cutI (fun z=>F z a) i x) μ ∧ cutI (fun z=>∫ a,F z a∂μ) i x=∫ a,cutI (fun z=>F z a) i x∂μ:=by
 have hz(z:ℂ)(g:z∈rim):update x i z∈hill I:=fill_I hx i (ball_subset_closedBall g)
 obtain ⟨H,h⟩:=windInt μ (fun v=> F (update x i v)) (fun j=>(hp j).circle hx i) hv (fun x hx=>hm _ (hz _ hx)) (fun x hx=>ht _ (hz _ hx)) 0 (mem_ball_self zero_lt_one)
 simp only [(fun a:A=> (mitt (hp a) hx i).deriv)] at h H
 exact ⟨H,(mitt (riverSum μ F hp hv hm ht) hx i).deriv.symm.trans h.deriv⟩
-- river manip
variable {f g:Key I→E}
abbrev dune(i:I):Key I→Key I:=fun v=> update v i 0
lemma River.fed (h:River f)(Z:ℂ)(i:I)(p:Z∈closedBall (0:ℂ) 1): River (fun y=>f (update y i Z)):=by
 refine ⟨h.shore.comp (((continuous_update (A:=fun _:I=>ℂ) i).comp ((continuous_id' (X:=Key I)).prodMk continuous_const)).continuousOn) (fun _ q=>fill_I q i p),fun u q j z hz=>?_⟩
 by_cases v:i=j; subst j; simpa [Function.update_idem] using (differentiableAt_const (𝕜:=ℂ) (c:=f (update u i Z)) (x:=z)) -- tune
 simp_rw [Function.update_comm (Ne.symm v)] -- orientation
 exact h.slope _ (fill_I q i p) j z hz
lemma River.stay (h:River f)(i:I): River (f ∘ dune i):=h.fed 0 _ (mem_closedBall_self zero_le_one)
lemma River.scale (h:River f)(v:ℂ): River (fun i=>v • f i):=⟨continuousOn_const.smul h.shore,fun j p i z hz=> (show DifferentiableAt ℂ (fun _:ℂ=>v) z from differentiableAt_const _).smul (h.slope j p i z hz)⟩
lemma River.flow (h:River f)(i:I): River (cutI f i):=by
 obtain ⟨C,hC,H⟩:= h.budget
 letI : SecondCountableTopology ℝ:= inferInstance
 refine riverSum sky _ (fun θ=> (h.fed (homeB θ) _ (homeC _)).scale _) (integrable_const C) (fun z hz=>?_) ?_
 · exact (stayB h hz i).aestronglyMeasurable
 intro z hz t; rw [norm_smul,norm_inv,home_q,inv_one,one_mul]; exact H _ (fill_I hz _ (homeC _))
lemma rind_x(h:River f)(i:I){C:ℝ}(p:∀ i∈hill I,‖f i‖≤C)(z: Key I)(hz:z∈hill I):‖cutI f i z‖ ≤ C:=by
 rw [←(mitt h hz i).deriv]; nth_rw 1 [← div_one C]; exact norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one (h.circle hz i) (fun y hy=>p _ (fill_I hz i (sphere_subset_closedBall hy)))
end YM.CF.Mew
