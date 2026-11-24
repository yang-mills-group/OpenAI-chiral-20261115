import YM.SU5.Regis.Masonry
/-! variance of packed aggregate about tangent; no rates in actual 4d field theory. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
noncomputable section
namespace YM.Regis.Head
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 ProbabilityTheory Submodule
open Gleam Matrix Next.SectorChange Next.SectorChange.Gaussian Real
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
section variance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
private lemma summit (x:ℝ)(p:0≤x): (x/2)^2 ≤ Real.exp x:=by
 have h:=le_trans (le_add_of_nonneg_right (by norm_num)) (Real.add_one_le_exp (x/2)); apply (pow_le_pow_left₀ (by positivity) h 2).trans_eq; rw [sq, ← Real.exp_add]; congr 1; ring
lemma exp_dial (x:ℝ): x^2 ≤4*(exp x + exp (-x)):=by
 rcases le_total 0 x with h|h; · linarith only [summit x h, exp_pos (-x)]
 linarith only [summit (-x) (neg_nonneg.mpr h),exp_pos x]
local notation "μ" => stdGaussian E
private lemma centered0 (f:E→ℝ){M R:ℝ}(b:∀ x, |f x|≤ M)(u: ContDiff ℝ 1 f)(v:∀ x, ‖fderiv ℝ f x‖ ≤ R)(he:∫ x,f x ∂μ=0): Integrable (fun x=> (f x)^2) μ ∧ ∫ x,(f x)^2∂μ≤ 8*exp ((Real.pi/2)^2/2)*(1+R^2):=by
 let R':=sqrt (1+R^2); let T:= ((Real.pi/2)^2/2); have ht:0≤T:=by unfold T; positivity
 let aM:= sqrt (1+M^2); have hv:0<R':= sqrt_pos.2 (by positivity);
 have hp:R'^2=1+R^2:= sq_sqrt (by positivity); let t:=R'⁻¹; let g(a:ℝ)(x:E):= exp (a*f x)
 have h0:0≤M:=(abs_nonneg _).trans (b 0);
 have h₀(a:ℝ)(t':a^2=t^2):(∫ x,g a x∂μ) ≤ exp T:=by
    apply (gale f a b u v).trans (Real.exp_monotone ?_); rw [he,mul_zero,zero_add,mul_pow a,t',show R^2 * (t^2*(Real.pi/2)^2)/2 = T*((1+R^2)-1)*t^2 from (by unfold T; ring),mul_assoc];
    refine mul_le_of_le_one_right ht ?_; rw [← hp]; unfold t; rw [inv_pow,← div_eq_mul_inv,div_le_one (by positivity)]; linarith only
 have h1: Integrable (fun i:E=> (f i)^2) μ:= bree _ _ (a:=(M^2)) (u.continuous.measurable.pow_const _) (fun i=>by rw [abs_of_nonneg (sq_nonneg _) ,←sq_abs (f i)]; exact pow_le_pow_left₀ (abs_nonneg _) (b _) _)
 have hu: (∫ i,(f i)^2 ∂μ) ≤ (∫ i,4*R'^2*(g t i+g (-t) i)∂μ):=by
    apply integral_mono h1 (((puff _ f t u.continuous.measurable b).add (puff _ f (-t) u.continuous.measurable b)).const_mul _)
    intro i; refine le_trans ?_ (mul_le_mul_of_nonneg_left (exp_dial (t*f i)) (sq_nonneg R')|>.trans_eq ?_)
    · apply Eq.le; unfold t; field_simp
    simp only [Pi.add_apply,neg_mul]; ring
 refine ⟨h1,hu.trans ?_⟩; rw [hp,integral_const_mul,integral_add (puff _ f t u.continuous.measurable b) (puff _ f (-t) u.continuous.measurable b)]; exact (mul_le_mul_of_nonneg_left (add_le_add (h₀ t rfl) (h₀ _ (neg_sq t))) (by positivity)).trans_eq (by unfold T; ring)
lemma squareMaps (u v: E→ℝ){U V z w D:ℝ} (hu:∀ x,|u x| ≤ U)(hv:∀ x,|v x|≤ V)(gu: ContDiff ℝ 1 u)(gv:ContDiff ℝ 1 v)(zu:(∫ x,u x ∂μ)=z)(zv:(∫ x,v x ∂μ)=w)(q:∀ x, ‖fderiv ℝ u x‖ ≤ D)(p:∀ x, ‖fderiv ℝ v x‖ ≤ D): Integrable (fun x=>u x*v x) μ ∧ |(∫ x,u x*v x∂μ)-z*w| ≤8* exp ((Real.pi/2)^2/2)*(1+D^2):=by
 let f(x:E):= u x-z; let g(x:E):=v x-w; let K:= 8* exp ((Real.pi/2)^2/2)*(1+D^2)
 have h:=bree μ _ gu.continuous.measurable hu; have h':=bree μ _ gv.continuous.measurable hv
 obtain ⟨a,ah⟩:= ofCentered u gu q h hu zu; obtain ⟨b,bh⟩:= ofCentered v gv p h' hv zv
 have hT: Integrable (fun x=>u x*v x) μ:= bree _ _ (a:=U*V) (gu.continuous.mul gv.continuous|>.measurable) (fun i=>by rw [abs_mul]; exact mul_le_mul (hu i) (hv i) (abs_nonneg _) ((abs_nonneg _).trans (hu 0)))
 have hx : (∫ x,f x * g x∂μ)=(∫ x,u x*v x∂μ)-z*w:=by
    simp_rw [show ∀ x,f x*g x=u x*v x-w*u x-z*v x+z*w from fun x=>by unfold f g; ring]; rw [integral_add (f:=fun x=> u x*v x-w*u x-z*v x) ((hT.sub (h.const_mul w)).sub (h'.const_mul z)) (integrable_const _), integral_sub (f:=fun x=> u x*v x-w*u x) (hT.sub (h.const_mul w)) (h'.const_mul _), integral_sub hT (h.const_mul _), integral_const_mul,integral_const_mul,zu,zv]; simp; ring
 refine ⟨hT,hx ▸ ?_⟩; rw [←Real.norm_eq_abs];
 apply (norm_integral_le_of_norm_le ((a.add b).div_const (2:ℝ)) (ae_of_all (μ) (fun i=> (?_)))).trans
 swap; · change ‖f i*g i‖≤ ((f i)^2+(g i)^2)/2; rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]; nlinarith only [sq_abs (f i),sq_abs (g i),sq_nonneg (|f i|-|g i|)] -- token |-| 
 change (∫ x,(f x^2+g x^2)/2∂μ) ≤ _; rw [integral_div,integral_add a b]; linarith only [ah,bh] -- f g unfolds
where ofCentered (u:E→ℝ){U z D:ℝ}(p:ContDiff ℝ 1 u)(hu:∀ x, ‖fderiv ℝ u x‖≤ D)(g:Integrable u (stdGaussian E))(h:∀ x,|u x|≤ U)(b: (∫ x,u x∂stdGaussian E)=z): Integrable (fun x=>(u x-z)^2) (stdGaussian E) ∧ (∫ x,(u x-z)^2∂stdGaussian E) ≤ 8*exp ((Real.pi/2)^2/2)*(1+D^2):= centered0 (fun i=> u i-z) (M:=U+|z|) (fun x=>(abs_sub ..).trans (add_le_add (h x) (le_refl _))) (p.sub contDiff_const) (fun x=>by rw [fderiv_sub_const]; exact hu x) (by rw [integral_sub g (integrable_const _)]; simp [b])
end variance
variable {n:Side}{G:Gauge}{H:Bed}{η C S v δ : ℝ}{Z:PathData G}{I J:Type*}
namespace Etch
variable [Fintype I][Fintype J](A: Etch G I) (q:Clip)(o o': J→ Cover) (t t':J→Signed)
abbrev ensemble(A:Etch G I) (t:J→Signed)(o:J→ Cover): Etch G (J×I):= salix (fun i=> A.pose (t i) (o i)) (fun _=>1)
variable (B:Z.Bounds q η C S)(P:Attached H Z)(L:Floor H q n δ v)(O:Bid.Sworn H n G) {ρ:ℝ}
local notation "G'" =>wrap n
lemma mode_e (x:Altar G n) : (A.ensemble t o).sketch q ρ 0 x=A.layoutC q ρ t (G'∘o) x:=by unfold ensemble; rw [salix_s]; simp only [one_mul,posed_s]; rfl
lemma ensemble_h (x:Config G n): (A.ensemble t o).here ρ x= A.gallery ρ t (G'∘o) x:=by unfold ensemble; rw [salix_h]; simp only [one_mul,posed_p]; rfl
include O L
lemma ensemble_earns : (A.ensemble t o).muρ q B P ρ n = Fintype.card J*A.muρ q B P ρ n:=by
 change clouds B P _= _; rw [show ((A.ensemble t o).sketch q ρ (0:Site n))= _ from funext (A.mode_e q o t)]; have hx:= A.gallery_fee q (G'∘o) ρ t B P L O 1; rw [plumeCost,one_mul,one_mul, cloud_turn B P _ (A.planSmooth .. |>.continuous)] at hx; exact hx
abbrev climax (A:Etch G I) (q:Clip):= 8* exp ((Real.pi/2)^2/2)*(1+(A.lensLimit q 2)^2)
lemma ensemble_double (h:0 ≤ ρ)(v':ρ ≤ 2)(a:Injective (fun i=>G' (o i)))(c:Injective (fun i=>G' (o' i))) [Nonempty J]:
 |((A.ensemble t o).radial (A.ensemble t' o')).muρ q B P ρ n-(Fintype.card J*A.muρ q B P ρ n)^2| ≤ (Fintype.card J)* A.climax q:=by
 let H':= stamen B P n; let z:= Fintype.card J*A.muρ q B P ρ n
 let F(t:J→Signed)(o:J→ Cover)(i:stamen B P n):= A.layoutC q ρ t (G' ∘ o) i.val; let U:ℝ:= Fintype.card J*A.arc
 let N:ℝ:= Fintype.card J; let S:= A.lensLimit q 2; let R:= S * sqrt N
 have ht(t:J→Signed)(o): ∫ x: stamen B P n,F t o x ∂stdGaussian (stamen B P n)=z:=by unfold F; simp_rw [← mode_e]; exact A.ensemble_earns q o t B P L O
 have he(t:J→Signed)(o):ContDiff ℝ 1 (F t o):=(A.planSmooth ..).comp H'.subtypeL.contDiff
 have hf': A.lensLimit q ρ ≤ A.lensLimit q 2:=by unfold lensLimit rays; rw [abs_of_nonneg h, abs_of_nonneg (by norm_num : (0:ℝ)≤2)]; gcongr
 have hp(t:J→Signed)(o:J→ Cover)(a:Injective (fun i=>G' (o i)))(x:H'): ‖fderiv ℝ (F t o) x‖ ≤ R:=by
    let V:= A.layoutC q ρ t (G'∘o); let e:= fderiv ℝ V x.val; change ‖fderiv ℝ (V ∘ H'.subtypeL) x‖ ≤ R; rw [fderiv_comp x _ H'.subtypeL.differentiableAt]; rw [H'.subtypeL.fderiv] -- need?
    exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (norm_subtypeL_le H')).trans ((A.rays_steady q _ a ρ t x.val).trans (mul_le_mul_of_nonneg_right hf' (sqrt_nonneg _))))
    exact (A.planSmooth q _ ρ _).differentiable (by norm_num) _
 have hh(t:J→Signed)(o:J→ Cover)(x:H'): |F t o x|≤ U:=A.planBound ..
 have he' := (squareMaps (F t o) (F t' o') (hh t o) (hh t' o') (he ..) (he ..) (ht ..) (ht ..) (hp t o a) (hp t' o' c)).2
 let Q(x):= (F t o x)*(F t' o' x)
 change |(∫ x:H', ((A.ensemble t o).radial _).sketch q ρ 0 x.val ∂stdGaussian H')- _| ≤ _
 simp_rw [radial_s,mode_e A]; rw [sq]; apply he'.trans; change 8*_*(1+R^2) ≤ N*_; unfold R climax; rw [mul_pow, sq_sqrt (by unfold N; positivity), ← mul_assoc N]; let E:=8*exp ((Real.pi/2)^2/2); have he:N≥1:=Nat.one_le_cast.mpr Fintype.card_pos; change E*_≤_*E*(1+S^2); linarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ E from mul_nonneg (by norm_num) (exp_pos _|>.le))]
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.squareMaps
#print axioms YM.Regis.Head.Etch.ensemble_double
