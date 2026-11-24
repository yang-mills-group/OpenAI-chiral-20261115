import YM.SU5.FiniteGaugeData.Lapis.Mistral
/-! # Gaussian transfer to an occupied subspace. Need surface-area estimate independent of Hessian width, powers of thermal horizon (other than through precision).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology InnerProductSpace Matrix RealInnerProductSpace ContDiff BigOperators NNReal ENNReal
namespace Motif
open Real ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 {F: Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {C h:ℝ} (S:F →ₗᵢ[ℝ] E)
local notation "μ" => stdGaussian E
local notation "ν" => stdGaussian F
abbrev sweep (S:F →ₗᵢ[ℝ] E): E →L[ℝ] F:= ContinuousLinearMap.adjoint S.toContinuousLinearMap

lemma dusk (W:E →L[ℝ] F)(x:F): charFun (Measure.map W μ) x= charFun μ ((ContinuousLinearMap.adjoint W) x):=by rw [charFun_apply,charFun_apply,integral_map W.continuous.aemeasurable (by fun_prop)]; simp_rw [ContinuousLinearMap.adjoint_inner_right W]

lemma taxi: MeasurePreserving (sweep S) μ ν:=by
 let V:=S.toContinuousLinearMap; let W:= sweep S
 apply MeasurePreserving.mk W.continuous.measurable; apply Measure.ext_of_charFun; ext x
 rw [dusk W x,charFun_stdGaussian,charFun_stdGaussian]; unfold W sweep; rw [adjoint_adjoint]; rw [show S.toContinuousLinearMap x=S x from rfl,LinearIsometry.norm_map]
lemma revenue (E:Type*)[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] :
 Integrable (fun x:E=>‖x‖^2) (stdGaussian E) ∧ (∫ x:E,‖x‖^2 ∂stdGaussian E)=(Module.finrank ℝ E:ℝ):=by
 let μ':=stdGaussian E; let b:=stdOrthonormalBasis ℝ E; let q:=Module.finrank ℝ E
 let L(i:Fin q):StrongDual ℝ E:= InnerProductSpace.toDual ℝ E (b i); have he(i:Fin q) : ‖L i‖=1:=by unfold L; rw [LinearIsometryEquiv.norm_map, b.norm_eq_one]
 have hh(i:Fin q): MemLp (fun x=> L i x) 2 μ':= IsGaussian.memLp_dual μ' (L i) _ (by norm_num)
 have hz(i) : Integrable (fun x=> (L i x)^2) μ':= (hh i).integrable_sq; refine ⟨?_,?_⟩; swap
 · have ht(x:E): ‖x‖^2=∑ i:Fin q,(L i x)^2:=(b.sum_sq_inner_right x).symm -- tune
   simp_rw [ht]; rw [integral_finsetSum]; swap; · exact fun i _=> hz i
   have ha(i:Fin q): (∫ x,(L i x)^2∂μ')=1:=by
      have hg:= variance_dual_stdGaussian (L i); rw [variance_eq_integral (L i).continuous.measurable.aemeasurable,integral_strongDual_stdGaussian, he] at hg; simpa only [sub_zero, one_pow] using hg
   change ∑ i:Fin q,_=_; unfold μ' at ha; simp_rw [ha]; simp [q] -- tune
 have he:MemLp id 2 μ':=IsGaussian.memLp_two_id; exact (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).1 he
omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] in
lemma account (x:E) : ‖x - S (sweep S x)‖^2 = ‖x‖^2 - ‖sweep S x‖^2 :=by
 let y:= sweep S x; rw [norm_sub_sq_real]; have he: ⟪x,S y⟫= ‖y‖^2:= by change ⟪x,S.toContinuousLinearMap y⟫ = _; rw [← adjoint_inner_left,show S.toContinuousLinearMap.adjoint x=y from rfl]; exact real_inner_self_eq_norm_sq y -- tune
 rw [show sweep S x=y from rfl,he, LinearIsometry.norm_map]; ring
lemma voucher : let g(x:E):= ‖x-S (sweep S x)‖^2; Integrable g μ ∧ (∫ x,g x ∂μ)= (Module.finrank ℝ E:ℝ) - Module.finrank ℝ F := by
 intro g; obtain ⟨r,t⟩:= revenue E; obtain ⟨v,b⟩:= revenue F; let w(x:E):= ‖sweep S x‖^2; have hk:=taxi S; have hv: Integrable w μ:=hk.integrable_comp_of_integrable v; have he:g = fun x=>‖x‖^2 -w x:= funext (account S); rw [he]; refine ⟨r.sub hv,?_⟩; rw [integral_sub r hv,t,← b]; congr 1; have hx:=integral_map («μ»:=μ) (φ:=sweep S) (f:=fun x:F=>‖x‖^2) hk.measurable.aemeasurable (by rw [hk.map_eq]; exact v.aestronglyMeasurable); rw [hk.map_eq] at hx; exact hx.symm
-- operate solely in norm-billed distances, not in eq locations.
lemma fiscal {X:Type*}[MeasurableSpace X]{P:Measure X}[IsProbabilityMeasure P]
  {g:X→ℝ}{u:ℝ}(ht: Integrable g P)(hg:Integrable (fun x=>g x^2) P)(h:(∫ x,g x^2∂P) ≤ u) : (∫ x,g x∂P) ≤ √u:=by
 let r:=∫ x,g x∂P; let s (x:X):=(g x-r)^2; have he(x:X):s x=g x^2 +r^2-2*r*g x:=by unfold s; ring
 have hz: r^2 ≤ u:=calc
    _ ≤ ∫ x,g x^2∂P:= by have hx:0 ≤ ∫ x, s x∂P:= integral_nonneg (fun i=>sq_nonneg _); simp_rw [he] at hx; rw [integral_sub (show Integrable (fun x=>g x^2+r^2) P from hg.add (integrable_const _)) (ht.const_mul _), integral_add hg (integrable_const _),integral_const,integral_const_mul] at hx; simp only [probReal_univ,one_smul] at hx; linarith only [show (∫ x,g x∂P)=r from rfl, hx] -- linarith simplify
    _ ≤ u:=h
 exact (le_abs_self _).trans ((le_of_eq (Real.sqrt_sq_eq_abs _).symm).trans (Real.sqrt_monotone hz))
-- variance of scaled projector difference. Avoid group shrink factors from Hess weight's *scale*. Compare in W1.
omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma lens (c:ℝ)(x:E) : ‖x-c•S (sweep S x)‖ ≤ ‖x -S (sweep S x)‖ + ‖1-c‖*‖sweep S x‖:=by
 let y:= S (sweep S x); have hz: y-c•y=(1-c)•y:=(by rw [sub_smul,one_smul]); exact (norm_sub_le_norm_sub_add_norm_sub x y (c•y)).trans_eq (by rw [hz,norm_smul]; rw [show ‖y‖=‖sweep S x‖ from S.norm_map _]) -- real 1-c implicit
lemma issued (c:ℝ): let g:E→ℝ:=fun x=>‖x - c• S (sweep S x)‖; let M:ℝ:= Module.finrank ℝ E; let N:ℝ:= Module.finrank ℝ F; Integrable g μ ∧ (∫ x,g x ∂μ)≤ Real.sqrt (M-N)+‖1-c‖ * Real.sqrt N:=by
 intro g M N; obtain ⟨r,t⟩:=voucher S; have v:=taxi S; obtain ⟨u,h⟩:=revenue F; let W:= S.toContinuousLinearMap.comp (sweep S); let g'(x:E):=S (sweep S x); let Z(x:E):=‖x-g' x‖
 let Q(y:E):=‖sweep S y‖; have h1 : Integrable g' μ:= W.integrable_comp IsGaussian.integrable_fun_id -- tune
 have h2 : Integrable Q μ:= v.integrable_comp_of_integrable (IsGaussian.integrable_id.norm); have hΩ := Real.sqrt_nonneg N
 have hk:Integrable Z μ:= (IsGaussian.integrable_fun_id.sub h1).norm; have h3:Integrable g μ:= (IsGaussian.integrable_fun_id.sub (h1.smul c)).norm
 refine ⟨h3,(integral_mono h3 (hk.add (h2.const_mul _)) (lens S c)).trans ?_⟩
 simp only [Pi.add_apply]; rw [integral_add hk (h2.const_mul _),integral_const_mul]; apply add_le_add (fiscal hk r t.le); apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply fiscal h2 (v.integrable_comp_of_integrable u)
 have he:=integral_map (φ:=sweep S) (f:=fun x:F=>‖x‖^2) v.measurable.aemeasurable (by rw [v.map_eq]; exact u.aestronglyMeasurable)
 rw [v.map_eq,h] at he; exact he.ge -- tune sides
-- use transported function for adjusted area. convenient for upper only
abbrev drift (S:F→ₗᵢ[ℝ] E)(c:ℝ):ℝ:= Real.sqrt ((Module.finrank ℝ E:ℝ)-Module.finrank ℝ F)+‖1-c‖*Real.sqrt (Module.finrank ℝ F) -- unused S
lemma aboard (f:E→ℝ)(p:∀ x y, |f x-f y|≤ C*‖x-y‖)(c:ℝ)(u:Integrable f μ)(v: Integrable (fun y:F=> f (c•S y)) ν)(g:0≤C): (∫ y:F,f (c• S y) ∂ν) ≤ (∫ y,f y∂μ)+C*drift S c:=by
 let h(x:E):=c• S (sweep S x); let q:=taxi S; obtain ⟨r,t⟩:= issued S c; let T(x:E):=‖x-h x‖; let U:=f ∘ h; have ht:Integrable U μ:=q.integrable_comp_of_integrable v
 have he := integral_map (φ:=sweep S) (f:= fun y:F=> f (c• S y)) q.measurable.aemeasurable (by rw [q.map_eq]; exact v.aestronglyMeasurable)
 rw [q.map_eq] at he; rw [he]; apply sub_le_iff_le_add'.1; change (∫ x,U x∂μ) - (∫ x,f x∂μ) ≤ _; rw [← integral_sub ht u]; calc
    _ ≤ ∫ x,C*T x∂μ:= by apply integral_mono (ht.sub u) (r.const_mul _); intro x; change f (h x)-_ ≤ _; exact (le_of_abs_le (p (h x) x)).trans_eq (by change _=C*‖x-h x‖; rw [norm_sub_rev])
    _ ≤ _:= by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left t g
theorem theatre (g:E→ℝ)(p:∀ x y, |g x-g y|≤ C*‖x-y‖)(e:ContDiff ℝ 1 g)(q:∀ x, ‖g x‖≤ h)(V: F→ℝ)(c:ℝ)(hp:∀ y,V y=g (c•S y))(h0:0≤ C)(h1:|c| ≤ 2) : Integrable (exp∘V) ν ∧ (∫ y,exp (V y)∂ν) ≤ exp ((∫ x,g x∂μ) + C*drift S c + Motion.bill (2*C)) := by
 have hf:=Motion.starlet e q; have he:ContDiff ℝ 1 V:=by rw [show V = fun x=> g (c • S x) from funext hp]; exact e.comp (contDiff_const (c:=c) |>.smul S.toContinuousLinearMap.contDiff)
 have hq(x): ‖V x‖≤ h:=by rw [hp]; exact q _
 obtain ⟨V₁,V₂⟩:= Motion.starlet he hq; let W:ℝ≥0:=⟨2*C,by positivity⟩
 have lp: LipschitzWith W V:= by apply LipschitzWith.of_dist_le_mul; intro u v; rw [dist_eq_norm,dist_eq_norm,hp,hp]; refine (p _ _).trans ?_; rw [← smul_sub,← map_sub,norm_smul,LinearIsometry.norm_map]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h0).trans_eq; change C*(2*‖u-v‖)=(2*C)*‖u-v‖; ring
 have hv:=Motion.peak he (fun x:F=>norm_fderiv_le_of_lipschitz (x₀:=x) ℝ lp) hq; refine ⟨V₂,hv.trans (exp_monotone (add_le_add ?_ le_rfl))⟩; have he': V= fun x=> g (c • S x):=funext hp; rw [he']; exact aboard S g p c hf.1 (he' ▸ V₁) h0
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rankL{G:Type}[NormedAddCommGroup G][NormedSpace ℝ G]{U:E→ₗ[ℝ] G}{Y: G→ℝ}(f:ContDiff ℝ 1 Y)(r:ℝ)(p:∀ x, ‖U x‖≤‖x‖): ContDiff ℝ 1 (fun x=> Y (r • U x)):=by
 let K:=U.mkContinuous 1 (fun x=> (p x).trans_eq (one_mul _).symm); exact f.comp (show ContDiff ℝ 1 (fun x:E=> r • K x) from contDiff_const.smul K.contDiff)
end Motif
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Motif.theatre
