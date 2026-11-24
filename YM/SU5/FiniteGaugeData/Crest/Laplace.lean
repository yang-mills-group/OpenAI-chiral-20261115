import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-! # Unwrapped temporal generator Laplace prices, normalized reciprocal charge
  Our kernel uses p coordinate itself, i.e., one full zone in angular not cycle units.
  Every `integrated` below is BEFORE the `(2π)⁻¹` charge of inserting a mode.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Crest
open Function Filter FourierTransform MeasureTheory Set Real
open scoped Topology BigOperators FourierTransform

-- scalar price amplitude kernel. Under synthetic coordinates (real) convention.
def surge (w x : ℝ) : ℂ := Complex.exp (Complex.I*(w*x:ℝ))
@[simp] lemma surge_norm (w x) : ‖surge w x‖=1 := by simp [surge,Complex.norm_exp]
@[fun_prop] lemma surge_cont : Continuous (Function.uncurry surge) := by unfold uncurry surge; fun_prop
@[simp] lemma surge_left (w x y) : surge (w+x) y=surge w y*surge x y := by rw [surge,add_mul,Complex.ofReal_add,mul_add,Complex.exp_add]; rfl
@[simp] lemma surge_right (w x y) : surge w (x+y)=surge w x * surge w y := by rw [surge,mul_add,Complex.ofReal_add,mul_add,Complex.exp_add]; rfl
lemma surge_add_c (w x z) : surge w x * Complex.exp (z * ↑x) = Complex.exp ((Complex.I*w+z) * x) := by rw [surge, ←Complex.exp_add, Complex.ofReal_mul, ←mul_assoc,←add_mul]

lemma lined {f:ℝ→ℂ}(u w:ℝ)(h: IntegrableOn f (Iic u))(g: IntegrableOn f (Ioi w))(p:u=w) : Integrable f:=by subst w; apply integrableOn_univ.mp; rw [← union_compl_self (Iic u),compl_Iic]; exact h.union g
lemma surged (w:ℝ){f:ℝ→ℂ}(h:Integrable f): Integrable (fun x=> surge w x*f x):=h.bdd_mul (by exact (show Continuous _ from surge_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) (Eventually.of_forall (fun x=> (surge_norm w x).le)) -- tune

def spark (a x : ℝ) : ℂ := Complex.exp (-a*|x|:ℝ)
def zip (a x : ℝ) : ℂ := (↑(a^2+x^2:ℝ))⁻¹
def integrated (f : ℝ→ℂ) (w:ℝ) := ∫ x,surge w x*f x
@[fun_prop] lemma zip_cont (a:ℝ)(h:0<a): Continuous (zip a):= by unfold zip; fun_prop (disch:=intros; norm_cast; positivity)
@[fun_prop] lemma spark_cont (a:ℝ): Continuous (spark a):=by unfold spark; fun_prop

variable {a:ℝ}(h:0<a)
include h
lemma spark_paid : Integrable (spark a):=by
 refine lined 0 0 ?_ ?_ rfl
 · exact (integrableOn_exp_mul_complex_Iic (a:=(a:ℂ)) h 0).congr_fun (fun x (v:x≤0)=>by simp [spark,abs_of_nonpos v]) measurableSet_Iic
 exact (integrableOn_exp_mul_complex_Ioi (a:=-(a:ℂ)) (by simpa using neg_lt_zero.mpr h) 0).congr_fun (fun x (v:0<x)=>by simp [spark,abs_of_pos v]) measurableSet_Ioi -- by simpa using neg_neg...
lemma zip_paid : Integrable (zip a):=by
 have he(x:ℝ): zip a x= (((a:ℂ)^2))⁻¹ *((↑(1+(a⁻¹*x)^2:ℝ):ℂ))⁻¹:=by unfold zip; push_cast; rw [←mul_inv, show (a:ℂ)^2*(1+((a:ℂ)⁻¹*x)^2)=(a:ℂ)^2+(x:ℂ)^2 by have h: (a:ℂ)≠0:= (by exact_mod_cast h.ne'); field_simp]
 apply ((integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero h.ne')).ofReal.const_mul (((a:ℂ)^2))⁻¹).congr; exact Eventually.of_forall (fun x=>by change _ * (((1+(a⁻¹*x)^2)⁻¹:ℝ):ℂ)=_; simpa only [Complex.ofReal_inv] using (he x).symm)

lemma spark_cost (x: ℝ) : integrated (spark a) x=2*a*zip a x:=by
 let A:= (a:ℂ); let p:= Complex.I*x; let f:= fun y:ℝ=> surge x y*spark a y
 have hp: p.re=0:=by simp [p]
 have hv:0<(p+A).re :=by simp [hp,A,h]
 have hb:(p+-A).re<0:=by simp [hp,A,h]
 unfold integrated
 rw [←integral_add_compl (s:=Iic 0) measurableSet_Iic (surged x (spark_paid h)), compl_Iic];
 have hz: EqOn f (fun y=> Complex.exp ((p+A) * y)) (Iic 0):=fun y (e:y ≤ 0)=>by simp [f,spark,abs_of_nonpos e,p,A,surge_add_c]
 have hy: EqOn f (fun y=> Complex.exp ((p+-A)*y)) (Ioi 0):=fun y (e:0<y)=>by simp only [f,spark,abs_of_pos e,Complex.ofReal_mul, Complex.ofReal_neg,surge_add_c]; rfl
 change (∫ y:ℝ in Iic 0, f y)+(∫ y:ℝ in Ioi 0, f y)=_
 rw [show (∫ y:ℝ in Iic 0,f y)=_ from setIntegral_congr_fun measurableSet_Iic hz, show (∫ y:ℝ in Ioi 0,f y)=_ from setIntegral_congr_fun measurableSet_Ioi hy] -- match f?
 rw [integral_exp_mul_complex_Iic hv,integral_exp_mul_complex_Ioi hb]; simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
 have hz' : p+A≠0:=fun e=> by rw [e] at hv; exact lt_irrefl 0 hv -- fix
 have hy' : p+-A≠0:=fun e=> by rw [e] at hb; exact lt_irrefl 0 hb
 have he : ↑(a^2+x^2:ℝ) = (-p+A)*(p+A) := by unfold p A; push_cast; linear_combination (x:ℂ)^2*Complex.I_sq
 rw [zip, he, show -p+A= -(p+-A) by ring]; change _ = 2*A *_; field_simp; ring

local notation "φ" => (2*Real.pi:ℝ)
omit h in
lemma compass (f:ℝ→ℂ)(y:ℝ): 𝓕 f y= integrated f (-(φ*y)):=by
 rw [fourier_real_eq_integral_exp_smul]; unfold integrated; refine integral_congr_ae (Eventually.of_forall fun x=>?_); dsimp only;rw [smul_eq_mul,surge]; congr 2 <;> push_cast <;> ring
-- normalized derivative of Laplace without illicit nonintegrable t multiplier
lemma throughout (w:ℝ) : integrated (zip a) w= (Real.pi/a:ℝ) * spark a w:=by
 let z:= fun x:ℝ=> surge w x*zip a x; let f:= spark a
 have hz:0<φ:=by positivity
 have hs(y:ℝ) : 𝓕 f y=2*(a:ℂ)*zip a (φ*y):=by unfold f; rw [compass,spark_cost h]; simp [zip]
 have he:= integrable_comp_mul_left_iff (zip a) hz.ne'
 have ht: Integrable (𝓕 f):=by rw [funext hs]; exact ((zip_paid h).comp_mul_left' hz.ne').const_mul (2*a)
 have hX : integrated (𝓕 f) (φ*w)=f w:=by
    have hw := congr_fun ((spark_cont a).fourierInv_fourier_eq (spark_paid h) ht) w
    rw [fourierInv_eq_fourier_neg _ ,compass] at hw; simpa only [mul_neg,neg_neg] using hw -- fix
 let X:= integrated (zip a) w
 have hy : 2*(a:ℂ) * (((φ⁻¹:ℝ):ℂ)* X)=f w:=by
    refine Eq.trans ?_ hX; unfold integrated; rw [← Complex.real_smul]; unfold X integrated; change 2*(a:ℂ)*(φ⁻¹ • ∫ x:ℝ,z x)=_; rw [← abs_of_pos (inv_pos.mpr hz), ←Measure.integral_comp_mul_left z φ,←integral_const_mul]; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_ ; dsimp only; rw [hs]; unfold z; rw [show surge (φ*w) x=surge w (φ*x) by unfold surge; ring_nf]; ring -- tune abs_of_pos occurrence
 change X= ↑(Real.pi/a:ℝ)*f w; rw [←hy]; push_cast
 have ht: (Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_pos.ne'
 have hp: (a:ℂ)≠0:=by exact_mod_cast h.ne'
 field_simp
end YM.CF.Crest
#print axioms YM.CF.Crest.throughout
