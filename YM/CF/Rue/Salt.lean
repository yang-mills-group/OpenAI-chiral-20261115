import YM.CF.Scree.Tune
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{n:Side}{t:ℝ}
open Jet
section lip
variable{E F A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][TopologicalSpace A]{B:Set E}{U:A→E→F}{x:E}{a:A}{k:ℕ}{C D:ℝ}
lemma value_joint (h:IsOpen B)(p:∃ C:ℝ,∀ a x,x∈ B → Allows (k+1) (U a) x C)(v:∀ i∈ B,Continuous fun y=>U y i) (a:A){x:E}(u:x∈B) : ContinuousAt (uncurry U) (a,x):=by
 obtain ⟨C,c⟩:=p; obtain ⟨b,f,S⟩:=Metric.mem_nhds_iff.mp (h.mem_nhds u); let H(t:A×E):=U t.1 t.2-U t.1 x; have hz:H (a,x)=0:= sub_self _; have he:ContinuousAt H (a,x):=by
    unfold ContinuousAt; rw [hz, tendsto_zero_iff_norm_tendsto_zero]; have hp : ContinuousAt (fun z:A×E=>C*‖z.2-x‖) (a,x):=by fun_prop
    apply squeeze_zero' (Eventually.of_forall fun z=> norm_nonneg (H z)); swap; · simpa [ContinuousAt] using hp
    filter_upwards [continuousAt_snd.tendsto.eventually (ball_mem_nhds (x:=x) f)] with y v
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun z p=>(c y.1 _ (S p)).smooth.differentiableAt (by simp)) (fun z p=> (c y.1 _ (S p)).slide.value) (convex_ball ..) (mem_ball_self f) v
 convert! he.add ((v x u).continuousAt.comp continuousAt_fst) using 1; simp only [uncurry_def,H,comp_def,Pi.add_def,sub_add_cancel]
-- difference quotients pointwise uniformly through genuine call; submit shoots
lemma quota_v (h:IsOpen B)(hp:∀ i∈ B,∀ a, Allows (k+2) (U a) i C)(ht:∀ i∈ B,Continuous (fun a=> U a i))(v:x∈ B)(z:E): Continuous (fun a=> fderiv ℝ (U a) x z):=by
 apply continuous_iff_continuousAt.mpr; intro w; obtain ⟨r,g,h⟩:= Metric.mem_nhds_iff.mp (h.mem_nhds v); let f(a:A):=(fderiv ℝ (U a) x) z; apply Metric.continuousAt_iff'.mpr; intro ε p -- tune
 have hv :0≤C:=(norm_nonneg _).trans (hp x v w).value; let b:=min (r/2) (ε/(4*(C*‖z‖+1))); have hq:0<b:=lt_min (by positivity) (by positivity); let t:= b/(2*(‖z‖+1)); have hT:0<t:=by positivity
 let y:= x+t • z; have hy:y-x=t • z:= add_sub_cancel_left ..; have hb:ball x b⊆B:= Set.Subset.trans (Metric.ball_subset_ball (le_trans (min_le_left ..) (by linarith : r/2 ≤ r))) h
 have hx:y∈ ball x b:=by rw [mem_ball, dist_eq_norm, hy,norm_smul,Real.norm_of_nonneg hT.le]; unfold t; have ht:0<(2:ℝ)*(‖z‖+1):=(by positivity); rw [div_mul_eq_mul_div,(div_lt_iff₀ ht)]; nlinarith [mul_nonneg hq.le (norm_nonneg z)]
 let c(a):=t⁻¹ • (U a y-U a x); have hc(a):dist (c a) (f a)≤ε/4:=by
    have hg : ∀ z∈ ball x b, Allows (k+2) (U a) z C:=fun j k=> hp _ (hb k) a
    have hw:= Convex.norm_image_sub_le_of_norm_fderiv_le' (φ:=fderiv ℝ (U a) x) (C:=C*b) (fun i p=> (hg i p).smooth.differentiableAt (by simp)) (fun i p=> ?_) (convex_ball ..) (mem_ball_self hq) hx; swap
    · apply (Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun i p=> (hg i p).slide.smooth.differentiableAt (by simp)) (fun i p=>(hg i p).slide.slide.value) (convex_ball ..) (mem_ball_self hq) p).trans; exact mul_le_mul_of_nonneg_left (by rw [mem_ball,dist_eq_norm] at p; exact p.le) hv
    have hu:= min_le_right (r/2) (ε/(4*(C*‖z‖+1)))
    have hr': b*(4*(C*‖z‖+1)) ≤ ε:= (le_div_iff₀ (by positivity : (0:ℝ)< 4*(C*‖z‖+1))).mp hu
    rw [hy,norm_smul,Real.norm_of_nonneg hT.le, map_smul] at hw; unfold c; rw [dist_eq_norm, ← inv_smul_smul₀ hT.ne' (f a),←smul_sub,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hT).le,inv_mul_le_iff₀ hT]; exact le_trans hw (by nlinarith only [mul_le_mul_of_nonneg_left hr' hT.le,mul_pos hT hq]) -- tune precedence
 have hK:Continuous c:=continuous_const.smul ((ht y (hb hx)).sub (ht x v))
 filter_upwards [(Metric.continuousAt_iff'.mp (hK.continuousAt (x:=w))) (ε/2) (by positivity)] with q h'
 linarith only [dist_triangle (f q) (c q) (f w),dist_triangle (c q) (c w) (f w),hc q,hc w,h',dist_comm (f q) (c q)] -- tune def
lemma tallK [FiniteDimensional ℝ E] (f:A→ E→L[ℝ] F)(h:∀ x:E,Continuous fun i=> f i x):Continuous f:=by
 let b:=Module.finBasis ℝ E
 let c(j: Fin (Module.finrank ℝ E)): E→L[ℝ]ℝ:= (b.coord j).toContinuousLinearMap
 let d(j: Fin (Module.finrank ℝ E))(i:A): E→L[ℝ]F:= ContinuousLinearMap.smulRight (c j) (f i (b j))
 have hd(j):Continuous (d j):=(ContinuousLinearMap.smulRightL ℝ E F (c j)).continuous.comp (h (b j))
 rw [show f = fun i:A=>∑ j,d j i from funext fun i=> ContinuousLinearMap.ext (fun x=>?_)]; exact continuous_finsetSum _ fun j _=> hd j
 rw [ContinuousLinearMap.sum_apply,←b.sum_repr x,map_sum]; simp only [map_smul,d,c,ContinuousLinearMap.smulRight_apply]; simp -- tune
variable [FiniteDimensional ℝ E]
lemma priorS (p:IsOpen B)(h:∀ a,∀ x∈ B,Allows (k+1) (U a) x C)(hp:∀ i∈ B,Continuous fun y=>U y i) (j:ℕ)(k':j≤k)(a:A){x:E}(u:x∈B):ContinuousAt (fun i:A×E=> iteratedFDeriv ℝ j (U i.1) i.2) (a,x):=by
 induction j generalizing F k with
 | zero=> simp_rw [iteratedFDeriv_zero_eq_comp]; exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuousAt.comp (value_joint p ⟨C,h⟩ hp a u)
 | succ j ih=> cases k; omega; next k=>
    simp_rw [iteratedFDeriv_succ_eq_comp_right]; have hv:= ih (F:=(E→L[ℝ] F)) (k:=k) (U:=fun a=>fderiv ℝ (U a)) (fun i j p=>(h i j p).slide) (fun i u=>tallK _ (quota_v p (fun j p i=>h i j p) hp u)) (by omega); exact LinearIsometryEquiv.continuousAt _ |>.comp hv
end lip
end YM.CF.Rue
