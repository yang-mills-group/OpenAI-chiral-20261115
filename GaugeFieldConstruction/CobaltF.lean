import GaugeFieldConstruction.IconF
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Flux
open Function Filter Metric NormedSpace Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
open YM.GaugeFieldConstruction CF.Crest CF.Crest.Shore MeasureTheory CF.Vale.Veins
open YM.Stationary (Gaia exileE earth_meas earth_bounded earth_oaks boundsEarth cartWeight geode_sum)
local notation "I"=> Complex.I
abbrev lightsU (p:Bin)(a:Axis):ℂ:= (Crest.Shore.weave p)^8 * (2*(p a:ℂ)/Crest.Shore.radius p)
abbrev RomanG (x:Cover)(i j:Cauchy.Spin)(p:Bin):ℂ:= mode (tmap p) x * tenderD i j (lightsU p)
variable {N :Side}(x:Cover)(i j:Cauchy.Spin)
lemma pays_r (z:Cover) : Measurable fun p:Gaia=> RomanG x i j (exileE p + stem z):=by
 unfold RomanG lightsU mode Crest.Shore.weave tenderD tmap Crest.Shore.radius; fun_prop
-- bound by sum
private abbrev siriP (i j:Cauchy.Spin)(a:Axis):= ‖Cauchy.Hij a i j‖
private lemma due_r (p:Bin)(z:Cover): ‖RomanG x i j (p+stem z)‖ ≤ ∑ a:Axis, ‖slat p z a‖ * siriP i j a:=by unfold RomanG; rw [norm_mul,mode_real _ _ (tmap_physical _),one_mul]; refine (norm_sum_le ..).trans_eq (sum_congr rfl fun a _=>?_); simp only [slat,norm_mul,norm_neg,Complex.norm_I,norm_star,one_mul] <;> rfl
lemma tinyH (p:Gaia)(v:p≠0)(a:Axis): ‖slat (exileE p) 0 a‖≤2/‖p‖:=by
 have he:‖Crest.Shore.weave (exileE p)‖≤1:=by unfold Crest.Shore.weave; rw [norm_prod]; apply prod_le_one (fun _ _=> norm_nonneg _) (fun _ _=>patched_norm _)
 have hx:‖(↑(exileE p a):ℂ)‖ ≤ ‖p‖:=by rw [Complex.norm_real]; exact PiLp.norm_apply_le p a
 have hg:Crest.Shore.radius (exileE p)=‖p‖^2:= Stationary.geode_sum p
 unfold slat; rw [show stem (0:Cover)=(0:Bin) from (by ext; simp [stem]),add_zero,norm_mul,norm_div,norm_pow,_root_.norm_mul,hg, Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),Complex.norm_ofNat]; have hp:0<‖p‖:=norm_pos_iff.mpr v
 rw [Complex.norm_real] at hx
 refine (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) he)).trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by norm_num)) (sq_nonneg _)).trans_eq (by field_simp))
lemma local_C (p:Bin)(z:Jill.Bound Real.pi p)(v:p≠0) : gyroP x i j p= shelved (RomanG x i j) p:=by
 unfold shelved gyroP RomanG tenderD tough
 simp_rw [map_stem,mode_phase,mode_periodic,mul_one,←tsum_mul_left, ← tsum_mul_right]
 conv_rhs=> rw [tsum_mul_left]
 rw [Summable.tsum_finsetSum]; rfl
 intro a _; exact (((spending (a:=a) z v).of_norm.mul_left _).mul_right _)
lemma Aqueduct : Integrable (RomanG x i j ∘ exileE) MeasureTheory.volume ∧ RomT x i j=(cartWeight:ℂ)*∫ p:Gaia, RomanG x i j (exileE p):=by
 let f:=RomanG x i j; let X(s:Cover)(p:Gaia):ℂ:= f (exileE p+stem s)
 have H₁:∀ᵐ p:Gaia ∂μ0, Bound Real.pi (exileE p) ∧ p≠0:=by filter_upwards [ae_restrict_mem earth_meas, ae_restrict_of_ae (show ∀ᵐ x:Gaia,x≠0 from by rw [ae_iff]; rw [show {x: Gaia|¬ x≠0}={0} from by ext; simp,measure_singleton])] with x h w; exact ⟨(pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr (fun i=> abs_le.mpr ⟨(h i).1.le,(h i).2⟩),w⟩
 choose C k d using boundC; let D:=∑ a:Axis,C a*siriP i j a; let E:=2*∑ a:Axis,siriP i j a
 have he{z:Cover}(x':z≠0):∀ᵐ p:Gaia ∂μ0, ‖X z p‖ ≤ income z*D:=by
    filter_upwards [H₁] with p h; apply le_trans (due_r x i j (exileE p) z); unfold D; rw [mul_sum]; refine sum_le_sum fun l _=>?_ ; apply (mul_le_mul_of_nonneg_right (d l _ h.1 (fun u=> h.2 (exileE.injective u)) z x') (norm_nonneg _)).trans_eq; ring
 have hp:∀ᵐ p:Gaia ∂μ0,‖X 0 p‖ ≤ E/‖p‖:=by
    filter_upwards [H₁] with p h; apply le_trans (due_r x i j (exileE p) 0); unfold E; rw [mul_sum, sum_div]; refine sum_le_sum fun l _=>?_ ; exact (mul_le_mul_of_nonneg_right (tinyH p h.2 l) (norm_nonneg _)).trans_eq (by ring)
 haveI: IsFiniteMeasure μ0:=⟨by rw [show μ0 _=MeasureTheory.volume boundsEarth by simp [μ0]]; exact lt_of_le_of_ne le_top earth_oaks⟩
 have hu(z:Cover):Integrable (X z) μ0:=by by_cases c:z=0; subst z; exact (pitφ E).mono' (pays_r x i j _).aestronglyMeasurable hp; exact (integrable_const _).mono' (pays_r x i j _).aestronglyMeasurable (he c)
 have hw(z:Cover):= (hu z).norm
 let V(z:Cover):ℝ:= ∫ p:Gaia, ‖X z p‖ ∂μ0
 have hw : Summable V:=by
    let L(z:Cover):= μ0.real Set.univ*(income z*D)
    let g(z:Cover):= L z+ (Pi.single 0 (V 0): Cover→ℝ) z
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=> norm_nonneg (X i _))) (f:=g) ?_ ((((wallet.mul_right D).mul_left (μ0.real Set.univ))).add (hasSum_pi_single ..).summable)
    intro z; by_cases h:z=0
    · subst z; unfold g; rw [Pi.single_eq_same]; apply le_add_of_nonneg_left; unfold L; have hp:=income_2 (0:Cover); have ht:0≤D:=sum_nonneg fun i _=> mul_nonneg (k _).le (norm_nonneg _); exact mul_nonneg (ENNReal.toReal_nonneg) (mul_nonneg hp.le ht)
    unfold g; rw [Pi.single_eq_of_ne h,add_zero]
    exact (integral_mono_ae (hw z) (integrable_const _) (he h)).trans_eq (by rw [integral_const]; rfl)
 obtain ⟨W,G⟩:= echoRev (f:=f) hu hw
 refine ⟨W, (congrArg ((cartWeight:ℂ)*·) ((integral_congr_ae (H₁.mono (?_))).trans G))⟩ -- tune
 exact fun p h=> local_C x i j _ h.1 fun u=> h.2 (exileE.injective u)
#print axioms Aqueduct
end YM.CF.Fock.Flux
end
