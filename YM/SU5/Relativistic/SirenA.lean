import YM.SU5.Relativistic.TrailingPrice
/-! # transverse pulse in normalized Haar, finite test Bessel. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest -- no Fock
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ENNReal
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
attribute [local instance] screen_fin
abbrev atlasCost : ℝ:= (((2*Real.pi)^3))
lemma atlasCost_p : 0<atlasCost:=by unfold atlasCost; positivity
lemma worth_eye : eyeMeasure Set.univ = ENNReal.ofReal (atlasCost):=by
 unfold atlasCost eyeMeasure; rw [Measure.pi_univ]; simp only [Measure.restrict_apply_univ,screen,Real.volume_Ioc,prod_const,card_univ,Fintype.card_fin]
 rw [show π- -π=2*π by ring, ENNReal.ofReal_pow (by positivity : (0:ℝ)≤φ)] -- duplicate
noncomputable def jEye:=ENNReal.ofReal atlasCost⁻¹ • eyeMeasure
instance : IsProbabilityMeasure jEye:=⟨by rw [jEye,Measure.smul_apply,worth_eye]; change ENNReal.ofReal _*_=_; rw [←ENNReal.ofReal_mul (inv_nonneg.mpr atlasCost_p.le), inv_mul_cancel₀ atlasCost_p.ne',ENNReal.ofReal_one]⟩
lemma gauge_true (x:WalkA)(f:Behind→ℂ):gaugeRead x f=∫ i,spax x i*f i∂jEye:=by
 unfold gaugeRead jEye; rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr atlasCost_p.le),Complex.real_smul]; unfold atlasCost; push_cast; ring
lemma eyeWithin : ∀ᵐ i:Behind ∂jEye,i∈backPane:=by
 have hx: Φ ∈ ae ((volume:Measure ℝ).restrict screen) := (ae_restrict_mem paneM).mono (fun _ p=> Ioc_subset_Icc_self p)
 have ht : ∀ᵐ i:Behind ∂eyeMeasure,i∈backPane:=by unfold eyeMeasure; apply Measure.ae_pi_le_pi; exact Filter.pi_mem_pi Set.finite_univ (fun _ _=>hx)
 apply ht.filter_mono; unfold jEye; exact Measure.ae_smul_measure_le _
@[fun_prop] lemma spax_cont (x:WalkA):Continuous (spax x):= continuous_finsetProd _ fun i _=> surge_cont.comp (continuous_const.prodMk (continuous_apply i))
lemma spax_norm(x:WalkA)(t:Behind):‖spax x t‖=1:=by unfold spax; simp
lemma spaxStar(x:WalkA)(t:Behind):star (spax (-x) t)=spax x t:=by
 unfold spax; rw [star_prod]; apply prod_congr rfl; intro i hi; simp only [Complex.star_def,←Complex.exp_conj,surge,Pi.neg_apply]; congr 1; simp

lemma eyeLease(x y:WalkA) : gaugeRead x (spax (-y))= if x=y then 1 else 0:=by
 unfold gaugeRead spax eyeMeasure; simp_rw [←prod_mul_distrib]; rw [integral_fintype_prod_eq_prod (E:=fun _:Fin 3=>ℝ) (μ:=fun _=>volume.restrict screen) (f:= fun i t=> surge (↑(x i):ℝ) t*surge (↑((-y: WalkA) i):ℝ) t)]
 have hp(k l:ℤ): pluse k (fun t=> surge (↑(-l:ℤ):ℝ) t)= (φ:ℂ)*(if k=l then 1 else 0):=by -- φ coercion
    have ht:=sound_wrap k l; unfold wrapT at ht; change pluse _ _=_; rw [← ht,Int.cast_neg]; change _ = _*( _ * _); have hz:(2*(Real.pi:ℂ))=(↑(φ:ℝ):ℂ):=by push_cast; rfl
    rw [hz,←mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (show φ ≠0 by positivity)),one_mul]; rfl
 change _*∏ i:Fin 3, pluse (x i) (fun t=> surge (↑(-(y i):ℤ):ℝ) t)=_; simp_rw [hp]
 by_cases p:x=y
 · subst y; simp [pi_pos.ne']
 rw [if_neg p]; obtain ⟨i,h⟩:= Function.ne_iff.mp p; apply mul_eq_zero_of_right; exact Finset.prod_eq_zero (mem_univ i) (by simp [h]) -- inspect
noncomputable def sonet(x: WalkA) : MemLp (spax (-x)) 2 jEye:= MemLp.of_bound (spax_cont (-x)).aestronglyMeasurable 1 (Eventually.of_forall fun k=>(spax_norm _ _).le) -- Prop def
abbrev mark(x:WalkA): Lp ℂ 2 jEye:= (sonet x).toLp (spax (-x))
lemma coincide (x:WalkA) (f:Behind→ℂ)(h:MemLp f 2 jEye):gaugeRead x f=inner ℂ (mark x) (h.toLp f):=by
 rw [gauge_true,L2.inner_def]; refine integral_congr_ae ?_; filter_upwards [h.coeFn_toLp,(sonet x).coeFn_toLp] with i e v; unfold mark; rw [v,e, RCLike.inner_apply', show starRingEnd ℂ (spax (-x) i)= _ from spaxStar x i]
lemma foundation : Orthonormal ℂ mark := by
 rw [orthonormal_iff_ite]; intro i j; exact (coincide _ _ _).symm.trans (eyeLease i j)
lemma lobe_size (S: Finset WalkA)(f:Behind→ℂ)(h:MemLp f 2 jEye)(B:ℝ)(hf:∀ k∈ backPane,‖f k‖≤ B): (∑ x∈S,‖gaugeRead x f‖^2) ≤ B^2:=by
 let U:=h.toLp f
 simp_rw [coincide _ _ h]; have he:‖U‖^2 ≤ B^2:=by
    rw [← inner_self_eq_norm_sq (𝕜:=ℂ),L2.inner_def]
    rw [← integral_re (L2.integrable_inner U U)]
    apply (integral_mono_ae (L2.integrable_inner (𝕜:=ℂ) ..|>.re) (integrable_const (c:=B^2)) _).trans (by simp)
    filter_upwards [h.coeFn_toLp,eyeWithin] with x i k; unfold U; change RCLike.re (K:=ℂ) _ ≤ _; rw [inner_self_eq_norm_sq]; rw [i]; gcongr; exact hf x k
 have hp:= Orthonormal.sum_inner_products_le (s:=S) U foundation -- tune orient
 exact hp.trans he
end YM.CF.Crest.Sleet
