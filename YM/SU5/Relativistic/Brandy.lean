import YM.SU5.Relativistic.Glacier
/-! # reading before boundaries on Laurent phase cost -/
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free Asymptotics
open Laurent Bloch Fir Jill Ember Shore UnitAddTorus
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
abbrev Dish:= UnitAddTorus Axis
def ingot (x:Bin) := dress Axis ((φ)⁻¹ • x)
lemma ingot_a(x y:Bin) : ingot (x+y)= ingot x+ingot y:=by unfold ingot; rw [smul_add]; ext1 i; exact AddCircle.coe_add ..
@[simp] lemma ingot0 : ingot 0=0:=by unfold ingot; rw [smul_zero]; rfl
lemma ingot_s: Surjective ingot:=by intro x; obtain ⟨y,rfl⟩:= fashion Axis x; refine ⟨(φ) • y,?_⟩; unfold ingot; rw [inv_smul_smul₀ (by positivity)]

def waffles (f:Bin→ℂ) (x:Dish):= f ((ingot_s x).choose)
def Pouch (f:Bin→ℂ):Prop := ∀ x z,f (x+stem z)= f x
lemma Pouch.wishes {f:Bin→ℂ}(h:Pouch f)(x:Bin) : waffles f (ingot x)= f x:=by
 let y:= (ingot_s (ingot x)).choose; have he:= (ingot_s (ingot x)).choose_spec
 have H (i:Axis) : ∃ z:ℤ, y i = x i + φ*z:=by
    obtain ⟨k,hk⟩:= AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp (show (((φ)⁻¹*y i:ℝ):UnitAddCircle) = (((φ)⁻¹*x i:ℝ):UnitAddCircle) from congrFun he i)); simp only [zsmul_eq_mul,mul_one] at hk; refine ⟨k,?_⟩; -- sign
    field_simp at hk; linarith only [hk]
 choose z hz using H; change f y = f x; rw [show y=x+ stem z from funext hz]; exact h x z
lemma toCream {f:Bin→ℂ}(p:Pouch f)(h:Continuous f): Continuous (waffles f):=by
 apply ((dressed Axis).continuous_iff).mpr; have he(z:Bin): waffles f (dress Axis z)=f ((φ) • z):=by rw [← p.wishes, ingot,inv_smul_smul₀ (by positivity)]
 rw [show waffles f ∘ dress Axis = (fun z=> f ((φ) • z)) from funext he]; fun_prop
lemma flashes (x:Bin)(i:Cover):mFourier i (ingot x)= mode (tmap x) i:=by
 unfold ingot; rw [wears]; congr 1; ext1 j; unfold walk tmap; simp only [Pi.smul_apply,smul_eq_mul]; push_cast; field_simp
lemma countM(i:Cover)(x y:Dish): mFourier i (x+y)= mFourier i x*mFourier i y:=by
 obtain ⟨x,rfl⟩:=ingot_s x; obtain ⟨y,rfl⟩:= ingot_s y; rw [←ingot_a,flashes,flashes,flashes,show tmap (x+y)= tmap x+tmap y from funext fun i=>Complex.ofReal_add ..,mode_phase]
lemma twoCream (x:Dish)(i:Cover):mFourier i x*mFourier (-i) x=1:=by rw [←mFourier_add,add_neg_cancel,mFourier_zero,ContinuousMap.one_apply]
abbrev potter (f:Dish→ℂ) (n:Cover):= mFourierCoeff f n
lemma whirlCream (n:Cover)(f:Dish→ℂ)(z:Dish): potter (fun x=> f (x+z)) n = mFourier n z * potter f n:=by
 change (∫ x:Dish,mFourier (-n) x*f (x+z) ∂globe Axis)=_*(∫ x:Dish,mFourier (-n) x*f x ∂globe Axis)
 rw [← integral_add_right_eq_self (fun x:Dish=>mFourier (-n) x*f x) z, ← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun i=>?_); dsimp only; rw [countM]; change _= mFourier n z*(_*_); linear_combination -(mFourier (-n) i)*f (i+z)*twoCream z n

def chill (i:Axis)(f:Bin→ℂ) (x:Bin):= fderiv ℝ f x (step i)
private def branch (x:Bin)(i:Axis)(u:ℝ):= x+u • (step i:Bin)
private lemma gest {g:Bin→ℂ}(p:Differentiable ℝ g)(x:Bin)(i:Axis)(u:ℝ): HasDerivAt (fun v=> g (x+v • step i)) (chill i g (branch x i u)) u:=by
 let W(v:ℝ):=branch x i v; have he: HasDerivAt W (step i) u:=by
    unfold W branch; convert ((hasDerivAt_id' u).smul_const (step i:Bin)).const_add x using 1 <;> first|simp|rfl
 exact (p (branch x i u)|>.hasFDerivAt).comp_hasDerivAt u he
lemma Pouch.jets {f:Bin→ℂ}(p:Pouch f)(h:Differentiable ℝ f)(i:Axis): Pouch (chill i f):=by
 intro x z
 have h₀:= gest h x i 0; have hf:=gest h (x+stem z) i 0
 rw [show (fun v:ℝ=> f (x+stem z+v • step i))=(fun v=> f (x+v • step i)) from funext (fun y=> by rw [add_right_comm, p])] at hf
 simpa only [branch, zero_smul, add_zero] using hf.unique h₀
private lemma derCoal (i:Axis)(n:Cover): HasDerivAt (fun v:ℝ=> mFourier n (ingot (v • step i))) (I*(n i:ℂ)) 0:=by
 let f:=fun v:ℝ=> I*(n i:ℂ)*↑v
 have hp(t:ℝ):mode (tmap (t • step i)) n=Complex.exp (f t):=by
    unfold mode tmap; rw [Finset.sum_eq_single i]; congr 1; unfold f; simp [step,mul_left_comm,mul_comm,mul_assoc] -- tune
    · intro j _ h; simp [h]
    simp
 simp_rw [flashes,hp]
 have hv:HasDerivAt (fun v:ℝ=> (v:ℂ)) 1 0:=by simpa using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x:=0)
 simpa only [f, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one] using (hv.const_mul (I*↑(n i))).cexp
lemma rise {n:ℕ}{f:Bin→ℂ}(h:ContDiff ℝ (↑(n+1:ℕ)) f) (i:Axis):ContDiff ℝ (↑n) (chill i f):=by apply ContDiff.clm_apply _ contDiff_const; exact h.fderiv_right (by exact_mod_cast le_rfl) -- tune
private lemma transder {f:Bin→ℂ}(p:Pouch f)(h:Differentiable ℝ f)(i:Axis)(n:Cover)(w:Continuous (chill i f)):
    potter (waffles (chill i f)) n= I * (n i:ℂ)*potter (waffles f) n:=by
 let g:= waffles f; let W:= waffles (chill i f); let A(t:ℝ)(x:Dish):= mFourier (-n) x*g (x+ingot (t • step i)); let B(t:ℝ)(x:Dish):=mFourier (-n) x*W (x+ingot (t • step i))
 have hv:Continuous g:=toCream p h.continuous; have hh:Continuous W:=toCream (p.jets h i) w
 have hx(t): Continuous (A t):= (mFourier _).continuous.mul (hv.comp (continuous_id.add continuous_const))
 obtain ⟨D,e⟩:= isCompact_univ.exists_bound_of_continuousOn hh.continuousOn; let μ:= globe Axis
 have hf:HasDerivAt (fun t=> ∫ x,A t x ∂μ) (∫ x,B 0 x ∂μ) 0 :=by
    letI : IsFiniteMeasure μ:= (by unfold μ; infer_instance)
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=μ) Filter.univ_mem (Eventually.of_forall (fun x=>(hx x).aestronglyMeasurable)) ((hx 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun x=> fun y t=>?_ ) (integrable_const (c:=D)) (Eventually.of_forall fun x=> fun y _=>?_ )).2 -- tune phantom
    · exact (mFourier _).continuous.mul (hh.comp (continuous_id.add continuous_const))
    · unfold B; rw [norm_mul]; refine le_trans (mul_le_of_le_one_left (norm_nonneg _) ((ContinuousMap.norm_coe_le_norm ..).trans (le_of_eq mFourier_norm))) (e _ (Set.mem_univ _))
    obtain ⟨x,rfl⟩:= ingot_s x; let r(t:ℝ):= branch x i t; unfold A B; simp_rw [←ingot_a]; -- tune binder
    unfold g W; simp_rw [p.wishes,(p.jets h i).wishes]; exact (gest h x i y).const_mul _
 have h₀ (x:ℝ): (∫ z:Dish,A x z ∂μ)= mFourier n (ingot (x • step i))*potter g n:= whirlCream n g _
 simp_rw [h₀] at hf; have hv':= hf.unique ((derCoal i n).mul_const _); unfold B at hv'; simp only [zero_smul,ingot0,add_zero] at hv'; exact hv'
lemma ascendCream {f:Bin→ℂ}{k:ℕ}(p:Pouch f)(h:ContDiff ℝ (↑k) f) (i:Axis):∃ A:ℝ,∀ n:Cover,((n i).natAbs:ℝ)^k * ‖potter (waffles f) n‖ ≤ A:=by -- beware nat exponent coercion first
 induction k generalizing f with
 | zero=>
    let F:C(Dish,ℂ):=⟨waffles f,toCream p h.continuous⟩; refine ⟨‖F‖,fun n=>?_⟩; simp only [pow_zero,Nat.cast_one,one_mul]; change ‖∫ x:Dish,mFourier (-n) x*F x∂globe Axis‖≤ ‖F‖; have hp(x:Dish):‖mFourier (-n) x*F x‖≤ ‖F‖:=by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (((mFourier _).norm_coe_le_norm _).trans (le_of_eq mFourier_norm))).trans (F.norm_coe_le_norm _)
    exact (norm_integral_le_of_norm_le_const (Eventually.of_forall hp)).trans (by simp)
 | succ k ih=>
    have he:= h.differentiable (by simp); obtain ⟨A,ht⟩:= ih (p.jets he i) (rise h i); refine ⟨A,fun n=>?_⟩; have hx:= ht n; rw [transder p he i n (rise h i).continuous] at hx; simpa only [norm_mul, Complex.norm_I,one_mul,←Complex.ofReal_intCast,norm_pow, Complex.norm_real, Real.norm_eq_abs,←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast,pow_succ,mul_assoc] using hx -- tune
end YM.CF.Crest.Sleet.Sorcerer
