import YM.SU5.Regis.Breeze
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis
open Function MeasureTheory Filter ProbabilityTheory Module
open scoped ContDiff Topology ENNReal BigOperators Classical NNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (f:E→ℝ) (y t C :ℝ) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
local notation "μ" => stdGaussian E
lemma kept (V:E→L[ℝ] F) (h:∀ x, ‖V.adjoint x‖=‖x‖) : MeasurePreserving V μ (stdGaussian F):=by
 refine ⟨V.continuous.measurable,Measure.ext_of_charFunDual ?_⟩
 funext a; obtain ⟨x,rfl⟩:= (InnerProductSpace.toDual ℝ F).surjective a; rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian]
 have ht: ((InnerProductSpace.toDual ℝ F x).comp V)= InnerProductSpace.toDual ℝ E (V.adjoint x):=ContinuousLinearMap.ext (fun y=> (ContinuousLinearMap.adjoint_inner_left V y x).symm)
 rw [show (InnerProductSpace.toDual ℝ F x) ∘SL V=_ from ht, LinearIsometryEquiv.norm_map,h,LinearIsometryEquiv.norm_map]
variable (S U:Submodule ℝ E)
lemma curt : MeasurePreserving S.orthogonalProjectionOnto μ (stdGaussian S):=by
 refine kept _ fun x=>?_ ; rw [← S.adjoint_subtypeL]; simp
lemma norm_g : Integrable (fun x:E=>‖x‖^2) μ ∧ (∫ x:E,‖x‖^2 ∂μ)=finrank ℝ E:=by
 let θ:= stdOrthonormalBasis ℝ E; let W(i:Fin (finrank ℝ E)):= InnerProductSpace.toDual ℝ E (θ i)
 have he(x:E):‖x‖^2= ∑ i,(W i x)^2:=by
    simp only [W,InnerProductSpace.toDual_apply_apply, ← OrthonormalBasis.sum_sq_inner_right θ x] -- check orientation
 have hf(i): Integrable (fun x:E=> W i x ^2) μ:= (IsGaussian.memLp_dual μ (W i) 2 (by norm_num)).integrable_sq
 have h(i):(∫ x:E,W i x^2 ∂μ)=1:=by
    have h:= variance_dual_stdGaussian (W i); rw [variance_eq_integral (W i|>.continuous.measurable.aemeasurable), integral_strongDual_stdGaussian] at h; simpa [W,θ.orthonormal.1 i] using h
 simp_rw [he]; exact ⟨integrable_finsetSum _ (fun i _=> hf i),by rw [integral_finsetSum _ (fun i _=> hf i)]; simp_rw [h]; simp⟩
lemma spool : Integrable (fun x:E=> ‖S.starProjection x‖^2) μ ∧ (∫ x, ‖S.starProjection x‖^2∂μ)=finrank ℝ S:=by
 have h:= norm_g (E:=S); let F:= S.orthogonalProjectionOnto
 have ht : (fun x=> ‖S.starProjection x‖^2)= (fun y:S=> ‖y‖^2)∘ (F:E→ S):= by funext x; rw [← Submodule.coe_orthogonalProjectionOnto_apply]; rfl
 -- rw integral function
 change Integrable _ _ ∧ integral (stdGaussian E) _=_
 rw [ht]; refine ⟨(curt S).integrable_comp_of_integrable h.1,Eq.trans ?_ h.2⟩
 change (∫ x, ‖F x‖^2 ∂μ)=(∫ x:S,‖x‖^2 ∂stdGaussian S); have p:MeasurePreserving F μ (stdGaussian S):= curt S; conv_rhs=>arg 1; rw [← p.map_eq]
 exact (integral_map p.aemeasurable (f:=fun x:S=> ‖x‖^2) (by fun_prop)).symm
lemma shedding (h:S ≤ U)(x:E): ‖U.starProjection x-S.starProjection x‖^2=‖U.starProjection x‖^2- ‖S.starProjection x‖^2:=by
 let s:= S.starProjection x; let u:= U.starProjection x
 have he:s=S.starProjection u:=(DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le h) x).symm
 change ‖u-s‖^2= ‖u‖^2- ‖s‖^2; rw [he]; have hx:= Submodule.norm_sq_eq_add_norm_sq_starProjection u S; rw [Submodule.starProjection_orthogonal_val] at hx; linarith
-- transfer uniform mean to fewer/recentered coords, loss at most o(V)+ κ |A|
variable {R M : ℝ} (b:∀ x,|f x|≤ M)(p: ContDiff ℝ 1 f)(l:∀ x, ‖fderiv ℝ f x‖ ≤ R)
lemma jumpk (p: ContDiff ℝ 1 f) (l:∀ x, ‖fderiv ℝ f x‖ ≤ R)(x y:E): |f x-f y|≤R*‖x-y‖:= by
 let c: ℝ≥0:= ⟨R,(norm_nonneg _).trans (l x)⟩; have h':LipschitzWith c f:= lipschitzWith_of_nnnorm_fderiv_le (p.differentiable (by simp)) (fun x=> l x); simpa only [dist_eq_norm, Real.norm_eq_abs, show (c:ℝ)=R from rfl] using (h'.dist_le_mul x y)
include b p l
-- want exp(-‖d‖²/2 etc) factoring. Let ≤ with D present intentionally.
def trend : ℝ := 1+ (Real.pi/2)^2/2
lemma impact (h:S ≤ U)(d:E):
 t*(∫ x,f (S.starProjection x+d)∂μ) ≤ t*(∫ x,f (U.starProjection x)∂μ)+R^2*t^2 + ‖d‖^2/2+((finrank ℝ U:ℝ)-(finrank ℝ S))/2:=by
 let a:= R^2*t^2+‖d‖^2/2; let u:=U.starProjection; let s:= S.starProjection
 let fQ(x:E):=t*f (s x+d); let fP(x:E):=t*f (u x);
 have hQ: Integrable fQ μ:= (bree _ (fun x=> f (s x+d)) ((p.continuous.comp (s.continuous.add continuous_const)).measurable) (fun x=> b _)).const_mul _
 have hP: Integrable fP μ:= (bree _ _ ((p.continuous.comp u.continuous).measurable) (fun x=> b _)).const_mul _
 let g(x:E):= ‖u x‖^2-‖s x‖^2; have H:Integrable g μ:= (spool U).1.sub (spool S).1; let k(x:E):= fP x + a + g x/2;
 have W:Integrable k μ:= (hP.add (integrable_const («μ»:=μ) a)).add (H.div_const 2); have w: fQ ≤ k:=by
    intro x; have hx:= l (u x); have hR:0≤R:= (norm_nonneg _).trans hx
    have hv : fQ x-fP x ≤ |t| * |f (s x + d)-f (u x)|:=by unfold fQ fP; rw [← abs_mul, ←mul_sub]; exact le_abs_self _
    have hl: ‖s x+d-u x‖ ≤ ‖u x-s x‖+ ‖d‖:= le_trans (by rw [show s x+d-_=(s x-u x)+d from (by abel)]; exact norm_add_le ..) (add_le_add (le_of_eq (norm_sub_rev ..)) (le_refl _)); have hf:= mul_le_mul_of_nonneg_left ((jumpk f p l _ _).trans (mul_le_mul_of_nonneg_left hl hR)) (abs_nonneg t)
    have ht: g x=‖u x-s x‖^2:= (shedding S U h x).symm; unfold k a; rw [ht]; nlinarith only [hv.trans hf, sq_nonneg (R*|t| - ‖u x-s x‖), sq_nonneg (R*|t| - ‖d‖), show R^2*|t|^2=R^2*t^2 from by rw [sq_abs]]
 have ht:= integral_mono hQ W w; unfold k at ht W; rw [integral_add (show Integrable (fun x=>fP x+a) μ from hP.add (integrable_const («μ»:= μ) _)) (H.div_const 2), integral_add hP (integrable_const («μ»:= μ) _), integral_const,probReal_univ, one_smul,integral_div] at ht; unfold g a fP fQ u s at ht; rw [integral_const_mul,integral_const_mul,integral_sub (spool U).1 (spool S).1,(spool U).2,(spool S).2] at ht; linarith
lemma swerve (h:S ≤ U)(d:E) :
 (∫ x: S, Real.exp (t*f (x.val+d))∂stdGaussian S) ≤ Real.exp (t*(∫ x,f (U.starProjection x)∂μ)+trend*R^2*t^2+ ‖d‖^2/2+((finrank ℝ U:ℝ)-(finrank ℝ S))/2):=by
 let V:= S.starProjection; let g:=fun x:E=> f (V x+d); have hG:ContDiff ℝ 1 g:=p.comp (V.contDiff.add contDiff_const)
 have hX(x): ‖fderiv ℝ g x‖≤R:=by
    have he: HasFDerivAt g ((fderiv ℝ f (V x + d)).comp V) x:=(p.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp x (V.hasFDerivAt.add_const d)
    rw [he.fderiv]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Submodule.starProjection_norm_le S)).trans (l _))
 let ρ:= (curt S); have he: (∫ x: S, Real.exp (t*f (x.val+d))∂stdGaussian S)= mgf g μ t:=by
    have hg:Continuous f:=p.continuous; unfold mgf; conv_lhs => arg 1; rw [←ρ.map_eq]
    exact integral_map ρ.aemeasurable (by fun_prop)
 rw [he]; refine le_trans (gale g t (fun i=> b _) hG hX) (Real.exp_monotone ?_)
 have H:= impact f t S U b p l h d; change t*(∫ x,g x∂μ)≤_ at H; unfold trend; linarith only [H]
end YM.Regis
#print axioms YM.Regis.swerve
