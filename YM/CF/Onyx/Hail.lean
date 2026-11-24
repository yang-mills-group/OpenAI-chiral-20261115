import YM.CF.Onyx.Hope
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open MeasureTheory GaussianFourier
open YM.Stationary (Gaia cartWeight)
-- Laplace/Fubini for the numerator via scalar potential, up to Fourier gamma factor. explicit units. 
variable {u:ℝ}{x:Gaia}
def fieldV (x:Gaia):= ‖x‖^2/4
def burn (x p: Gaia):=Complex.exp (Complex.I*inner ℝ x p)
def tog (u:ℝ)(p: Gaia):ℝ:= Real.exp (-u*‖p‖^2)
def pet (u:ℝ)(p: Gaia):ℝ:=tog u p/‖p‖^2
def house (u:ℝ)(p:Gaia):ℝ:=tog u p/‖p‖
def rafter(x:Gaia)(k:ℝ × Gaia):= burn x k.2*(tog k.1 k.2:ℂ)
lemma feld (x p:Gaia)(u:ℝ) : rafter x (u,p)= Complex.exp (-(u:ℂ)*‖p‖^2+Complex.I*inner ℝ x p):=by unfold rafter burn tog; push_cast; rw [← Complex.exp_add,add_comm]
lemma iron (x p:Gaia): ‖burn x p‖=1:=by unfold burn; rw [Complex.norm_exp]; simp
lemma helm(x p:Gaia)(u:ℝ) : ‖rafter x (u,p)‖=tog u p:=by unfold rafter; rw [norm_mul,iron,Complex.norm_real,Real.norm_of_nonneg (show 0<tog (u,p).1 (u,p).2 from Real.exp_pos _).le,one_mul]
lemma fare (x:Gaia)(h:0<u): Integrable (fun p=>rafter x (u,p)) ∧ (∫ p:Gaia, rafter x (u,p)) = (((Real.pi/u)^2 * Real.exp (-fieldV x/u):ℝ):ℂ):=by
 simp_rw [feld]; refine ⟨integrable_cexp_neg_mul_sq_norm_add (show 0<(u:ℂ).re from h) Complex.I x,?_⟩
 rw [integral_cexp_neg_mul_sq_norm_add (show 0<(u:ℂ).re from h),show Module.finrank ℝ Gaia=4 by simp [Stationary.Gaia,Axis]]; unfold fieldV; push_cast; rw [Complex.I_sq]; norm_num; left; congr 1; ring
lemma pearl (h:0<u): Integrable (tog u) ∧ (∫ p,tog u p)= (Real.pi/u)^2:=by
 have hg:=fare (0:Gaia) h; have hx:=hg.1.norm; have ht:(fun p:Gaia=>tog u p)=(fun p=> ‖rafter 0 (u,p)‖):=funext fun k=>(helm ..).symm; refine ⟨by rw [show tog u= _ from ht]; exact hx,?_⟩
 apply Complex.ofReal_injective; rw [show ((Real.pi/u)^2:ℝ)= ((Real.pi/u)^2*Real.exp (-fieldV 0/u):ℝ) from ?_] -- rw loop
 swap; · simp [fieldV]
 rw [←hg.2,←integral_complex_ofReal]; simp_rw [rafter,burn]; simp 
lemma headR(x:Gaia)(h:0<u) : Integrable (rafter x) ((volume.restrict (Set.Ioi u)).prod volume):=by
 rw [integrable_prod_iff (by unfold rafter burn tog; fun_prop)]; refine ⟨?_,?_⟩
 · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v e; exact (fare x (h.trans e)).1
 simp_rw [helm]; have he:= integrableOn_Ioi_rpow_of_lt (show (-2:ℝ)< -1 by norm_num) h
 apply Integrable.congr (he.const_mul (Real.pi^2)); filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw; rw [(pearl (h.trans hw)).2]; norm_num; rw [div_pow]; congr 1 -- tune
lemma harp (p:Gaia)(h:0<‖p‖)(u:ℝ): (∫ r in Set.Ioi u,tog r p)=pet u p:=by
 let G(r:ℝ):= -pet r p; have ht : Tendsto G atTop (𝓝 0):=by
    have he : Tendsto (fun w:ℝ=> -(w*‖p‖^2)) atTop atBot := tendsto_neg_atTop_atBot.comp ((tendsto_id (x:=atTop)).atTop_mul_const (by positivity)) -- tune
    simpa [G,pet,tog] using ((Real.tendsto_exp_atBot.comp he).div_const (‖p‖^2)).neg
 rw [integral_Ioi_of_hasDerivAt_of_nonneg' (g':=fun r=>tog r p) _ (fun r _=>(Real.exp_pos _).le) ht]; simp [G]; intro r hw; unfold G pet tog; have he:= ((((hasDerivAt_id' r).neg.mul_const (‖p‖^2)).exp).div_const (‖p‖^2)).neg; convert he using 1 <;> try rfl
 simp [h.ne']; field_simp
lemma roof(x p: Gaia)(e:p≠0)(u:ℝ): (∫ r in Set.Ioi u,rafter x (r,p)) = burn x p*pet u p:=by
 change ∫ r in Set.Ioi u,burn x p*(tog r p:ℂ)=_; rw [integral_const_mul,integral_complex_ofReal,harp _ (norm_pos_iff.mpr e)] -- tune
lemma pen (h:0<u): Integrable (pet u) ∧ Integrable (house u) :=by
 have he:= (headR 0 h).integral_norm_prod_right; simp_rw [helm] at he
 have hx :∀ᵐ p:Gaia,p≠0:=by rw [ae_iff]; simp -- tune
 have hp:Integrable (pet u):= he.congr (hx.mono fun i e=>harp i (norm_pos_iff.mpr e) _)
 refine ⟨hp,(hp.add (pearl h).1).mono' ?_ (hx.mono fun i e=>?_)⟩
 · unfold house tog; apply Measurable.aestronglyMeasurable; fun_prop
 have hz :0<‖i‖:=norm_pos_iff.mpr e; have hh:0<tog u i:=Real.exp_pos _; unfold house; rw [Real.norm_of_nonneg (by positivity)]; change _ ≤ tog u i / _+_; rcases le_total ‖i‖ 1 with l|l
 · exact (div_le_div_of_nonneg_left hh.le (pow_pos hz _) (by nlinarith : ‖i‖^2 ≤ ‖i‖)).trans (le_add_of_nonneg_right hh.le)
 exact (div_le_self hh.le l).trans (le_add_of_nonneg_left (show 0≤pet u i by unfold pet; positivity)) -- tune
end YM.CF.Onyx
