import YM.CF.Newt.Chain
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior Finset MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink FreeResolvent.TestD PhysicalNext.JointLoad.Heir Jet
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {X E F H:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
 [NormedAddCommGroup H][NormedSpace ℝ H]{a C K M r d s B D:ℝ}{x:E}{f g:E→F}{p:H→E}{n:ℕ}
lemma point_ne {x:H}(hp: Allows n p x (M*s))(hs:∀ w:E, ‖w‖<r→ Allows n f w C)(hf:1≤n)(h:0<s)(hw:0<M)(he:M*s ≤ 1)(hy:M*s < r):
 Allows n (fun u=> f (p u)- f 0) x (composeCost n (C*(M*s)) 1):=by
 let Z(u:E):=f ((M*s) • u)- f 0; let L(y:H):=(M*s)⁻¹ • p y; have hL:0<M*s:= mul_pos hw h
 have hr:Z ∘ L=(fun u=> f (p u)- f 0):=by ext x;  change f (((M*s) • ((M*s)⁻¹ • p x)))-_= _; rw [smul_inv_smul₀ hL.ne']
 rw [← hr]; have hT :=hp.smul ((M*s)⁻¹); rw [abs_of_nonneg (by positivity), inv_mul_cancel₀ hL.ne'] at hT
 have hx : ‖L x‖≤ 1:= hT.value
 exact (near_s (s:=M*s) (f:=f) hL.le he hf hy hs hx).comp hT
omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
lemma faction {g : E→ E→L[ℝ] H}{f:E→ F→L[ℝ] E}(hp:Allows n g x C)(hq:Allows n f x K) : Allows n (fun y=> (g y).comp (f y)) x (2^n*C*K):=by
 have he:= hp.bilinear (ContinuousLinearMap.compL ℝ F E H) hq (ContinuousLinearMap.norm_compL_le ..); rwa [mul_one] at he
omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] in
lemma fiction {u:E→ H→L[ℝ] H}{v:E→ F→L[ℝ] H}(hp:Allows n u x C)(hq:Allows n v x K) : Allows n (fun y=> (u y).comp (v y)) x (2^n*C*K):=by
 have he:= hp.bilinear (ContinuousLinearMap.compL ℝ F H H) hq (ContinuousLinearMap.norm_compL_le ..); rwa [mul_one] at he
lemma spirit {g:E × ℝ→ F}(h: Arc g n x)(hF:∀ t∈interval, Allows n (fun y=>g (y,t)) x C):
 Allows n (fun y=>∫ t in interval,g (y,t)) x C:=by
 let f(y):=∫ t in interval,g (y,t); have hC:0≤C:=(hF 0 ⟨le_rfl,zero_le_one⟩).nonneg; have hp:ContDiffAt ℝ n f x:=h.writes
 refine ⟨hp,fun i hi=> Planned.AtomRegular.op_le_of_unit hC fun w hw=>?_⟩
 let l:=List.ofFn w; have hh:l.length=i:= List.length_ofFn
 let L:ℝ→F:=fun t=> over id g l (x,t); have hz:iteratedFDeriv ℝ i f x w=∫ t in interval,L t:=by
    rw [show iteratedFDeriv ℝ i f x w= jet id f l x from (FreeResolvent.Stars.list_result id w f x).symm, Arc.report id _ (show Arc g l.length x from fun i ht=> (h i ht).of_le (by rw [hh]; exact_mod_cast hi))]
 have hu:Arc (over id g l) 0 x:= fun t ht=> over_smooth id l ((h t ht).of_le (by rw [hh,zero_add]; exact_mod_cast hi))
 rw [hz]
 apply (norm_integral_le_integral_norm _).trans
 have hr: IntegrableOn L interval:=hu.int
 calc
    _ ≤ ∫ _:ℝ in interval, C:= integral_mono_ae hr.norm (integrable_const _) ((ae_restrict_mem measurableSet_Icc).mono fun t ht=>?_)
    _ = _ := by simp [interval]
 unfold L over; dsimp only
 rw [show l=List.ofFn w from rfl, FreeResolvent.Stars.list_result]; simpa only [Function.id_comp,prod_const_one,mul_one] using (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le ((hF _ ht).norm_le i hi) hw)
-- opacity helpers
end YM.CF.Newt
