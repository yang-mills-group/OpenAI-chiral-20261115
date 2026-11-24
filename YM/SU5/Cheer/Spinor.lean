import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-! # The 2d Gaussian and its one Pearl moment. Generic all lifts. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex GaussianFourier MeasureTheory Measure
open scoped Real Topology NNReal ENNReal InnerProductSpace
variable (c:ℂ)
-- directly radian
abbrev SpinP:=ℂ
def bill (v:SpinP):ℝ:= ‖v‖^2
@[fun_prop] lemma bill_tel: Continuous bill:=(by unfold bill; fun_prop)
lemma bill_m (x y:SpinP): bill (x*y)=bill x*bill y:=by simp [bill,mul_pow]
lemma bill_p(x:SpinP):0 ≤ bill x:=sq_nonneg _
lemma bill_vis {x:SpinP}(h:x≠0) : 0<bill x:= pow_pos (norm_pos_iff.mpr h) _
local notation "μ"=> (volume : Measure SpinP)
local notation "π'"=> ((Real.pi:ℝ):ℂ)
def pearl (c:ℂ)(p:SpinP):=cexp (-(bill p:ℂ)*c)
def bevel (c:ℂ)(p:SpinP):=(bill p:ℂ)*pearl c p
@[fun_prop] lemma bill_mover (c:ℂ): Continuous (pearl c):=by unfold pearl; fun_prop
@[fun_prop] lemma bevel_cont (c:ℂ): Continuous (bevel c):=by unfold bevel; fun_prop
lemma raw (x p:ℂ): pearl x p = cexp (-x*(‖p‖:ℂ)^2):=by unfold pearl bill; push_cast; ring_nf
lemma pearl_norm (p x:ℂ): ‖pearl x p‖=Real.exp (- x.re * bill p):= by unfold pearl; rw [Complex.norm_exp]; simp; ring_nf
lemma pearl_shift (u:ℂ)(v:SpinP): pearl c v * pearl u v= pearl (c+u) v:= by unfold pearl; rw [mul_add, Complex.exp_add]
variable {c}(u:0<c.re)
include u
lemma ne_of_real_pos : c≠0:= by intro h; simp [h] at u
lemma pearl_get : (∫ v:SpinP, pearl c v)=π'/c:=by
 simp_rw [raw]; rw [integral_cexp_neg_mul_sq_norm u]; rw [show Module.finrank ℝ SpinP=2 from Complex.finrank_real_complex]; norm_num -- charge
lemma pearl_paid : Integrable (pearl c) μ:=by
 change Integrable (fun x => pearl c x); have ht:= integrable_cexp_neg_mul_sq_norm_add u (0:ℂ) (0:SpinP); simpa [raw] using ht 
lemma pearl_cut {v:ℝ}(h:0<v) (z:SpinP)(w:2*v ≤ c.re): ‖bevel c z‖ ≤ v⁻¹*‖pearl (v:ℂ) z‖:= by
 let t:=bill z; have ht:0≤t:= bill_p _; simp only [bevel,norm_mul, Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (bill_p _),pearl_norm,ofReal_re]; have he:t*v ≤ Real.exp (v*t):= calc
    t*v ≤ v*t+1:=by nlinarith
    _ ≤ _ := Real.add_one_le_exp _
 have hy : t * Real.exp (-v*t) ≤ v⁻¹ := by
    rw [neg_mul,Real.exp_neg,← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (Real.exp_pos _) h]; simpa
 change t*_ ≤ v⁻¹* Real.exp (-v*t)
 calc _ ≤ t * Real.exp (- (v*t)-v*t):= by
             apply mul_le_mul_of_nonneg_left _ ht
             apply Real.exp_le_exp.mpr; change -c.re*t ≤_; nlinarith
      _ = t* Real.exp (-v*t) * Real.exp (-v*t):=by rw [show -(v*t)-v*t= -v*t+ -v*t by ring, Real.exp_add]; ring 
      _ ≤ _:= mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
lemma bevel_gift : Integrable (bevel c) μ ∧ (∫ v:SpinP, bevel c v)=π'/c^2:=by
 let d:= c.re/4; have hd:0<d:=by unfold d; positivity
 let s: Set ℂ := {z|2*d< z.re}
 have hw:c ∈ s:=by change 2*(c.re/4) < _; linarith
 have hg:=hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=pearl) (F':=fun q=>-bevel q) (bound:=fun z=>d⁻¹ * ‖pearl (d:ℂ) z‖) («μ»:= μ) ((show IsOpen s from isOpen_lt continuous_const continuous_re).mem_nhds hw) (Eventually.of_forall fun i=> (bill_mover i).aestronglyMeasurable) (pearl_paid u) ((bevel_cont c).neg.aestronglyMeasurable) (ae_of_all _ fun v i hi=> (by simp only [Pi.neg_apply,norm_neg]; have he:2*d < i.re:=hi; exact pearl_cut (by linarith) hd v he.le)) ((pearl_paid (c:=(d:ℂ)) hd).norm.const_mul _) (ae_of_all _ fun v i _=> (by convert! (((hasDerivAt_id' i).const_mul (-(bill v:ℂ))).cexp) using 1; unfold bevel pearl; simp [mul_comm]))
 have hv : HasDerivAt (fun y:ℂ=> ∫ v:SpinP, pearl y v) (- (π'/c^2)) c := by
   have hr:= (hasDerivAt_const c π').div (hasDerivAt_id' c) (ne_of_real_pos u)
   have hh:HasDerivAt (fun y:ℂ=> π'/y) (- (π'/ c^2)) c:=by simp [neg_div] at hr; exact hr
   apply hh.congr_of_eventuallyEq; exact (((show IsOpen {z:ℂ | 0< z.re} from isOpen_lt continuous_const continuous_re).eventually_mem u).mono fun i e=> pearl_get e)
 have ht:= hv.unique hg.2; simp only [Pi.neg_apply, integral_neg] at ht; exact ⟨integrable_neg_iff.mp hg.1,(neg_inj.mp ht).symm⟩
end YM.Cheer
#print axioms YM.Cheer.bevel_gift
