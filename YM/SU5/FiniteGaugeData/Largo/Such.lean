import YM.SU5.FiniteGaugeData.Largo.Lyric
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir
open scoped Topology BigOperators Pointwise
variable (z:ℂ)(N:Side)(h:Odd N.val)
private lemma collar (z:ℂ): chip z=(2*Complex.I)*Complex.exp (Complex.I*z/2) * Complex.sin (z/2):=by
 let k:=Complex.I*z/2; unfold chip Complex.sin; rw [show z/2*Complex.I=k from (by unfold k; ring),show - (z/2)*Complex.I= -k from (by unfold k; ring)]; rw [show Complex.I*z= k+k from (by unfold k; ring), Complex.exp_add]; rw [show (k+k)/2=k from (by ring)]; ring_nf; simp only [Complex.I_sq,Complex.exp_neg]; field_simp; ring
include h in
lemma plank_g : plank N z * hsinc (z/2)= hsinc (N.val*z/2):=by
 by_cases p:z=0; · subst z; simp [hzero]
 let a:ℂ:= N.val; let x:= Complex.I*z/2; let i:= mid N; have hp:a≠0:=side_ne N; have hz:2*(i:ℂ)+1=a:=by unfold i a; exact_mod_cast mid_double N h
 unfold plank; rw [haway _ (div_ne_zero p (by norm_num)), haway _ (div_ne_zero (mul_ne_zero hp p) (by norm_num))]; have H:=rail_chip N z; rw [collar,collar] at H; have hw: twirl z (-i)*Complex.exp (a*x)= Complex.exp x:=by unfold twirl; rw [←Complex.exp_add]; push_cast; rw [←hz]; unfold x; ring_nf
 have hh:Complex.exp (Complex.I*(N.val*z)/2)= Complex.exp (a*x):=by unfold a x; ring_nf
 rw [hh] at H; change a*rail N z*((2*Complex.I)*Complex.exp x*Complex.sin (z/2))=2*Complex.I*Complex.exp (a*x)*Complex.sin (a*z/2) at H; nth_rw 1 [← hw] at H -- rewrite H? H not includes globe? x first
 have he: a*twirl z (-i)*rail N z*Complex.sin (z/2)=Complex.sin (a*z/2):=by
    apply mul_left_cancel₀ (mul_ne_zero (show 2*Complex.I≠0 by simp) (Complex.exp_ne_zero (a*x))); linear_combination H
 change twirl z (-i)*rail N z* _= _/(a*z/2); field_simp; rw [mul_comm z a]; linear_combination he -- tune
section
variable {X:Type*}{f:Filter X} {g:X→ℂ}{z:ℂ}{M:X→Side} (p:∀ x, Odd (M x).val)(r:Tendsto (fun i=> (M i).val) f atTop)
set_option quotPrecheck false
local notation "A" x:max=> (((M x).val:ℕ):ℂ)
include r
lemma getUp (h:Tendsto g f (𝓝 z)): Tendsto (fun x=> (A x)⁻¹ * g x) f (𝓝 0):= by
 have h':Tendsto (fun t:ℝ=>(t⁻¹:ℝ)) atTop (𝓝 0):= tendsto_inv_atTop_zero; have he:Tendsto (fun x=>(A x)⁻¹) f (𝓝 0):=by simpa [Function.comp_def] using! Complex.continuous_ofReal.continuousAt (x:=0)|>.tendsto.comp (h'.comp (tendsto_natCast_atTop_atTop.comp r))
 simpa using he.mul h
omit r in
lemma hingeSin (z:ℂ): z*hsinc z=Complex.sin z:=by
 by_cases p:z=0; · simp [p]
 rw [haway z p,mul_div_cancel₀ _ p]
lemma inward (h:Tendsto g f (𝓝 z)): Tendsto (fun x=> A x * Complex.sin ((A x)⁻¹*g x)) f (𝓝 z) :=by
 have he:= h.mul ((hschi.continuous.tendsto 0).comp (getUp r h)); simp_rw [←hingeSin, ←mul_assoc, mul_inv_cancel₀ (side_ne _),one_mul]; simp_rw [hzero,mul_one] at he; exact he
include p in
lemma plank_T (h:Tendsto g f (𝓝 z)): Tendsto (fun x=> plank (M x) ((A x)⁻¹ * g x)) f (𝓝 (hsinc (z/2))):= by
 let Y(x):= hsinc ((A x)⁻¹*g x/2); have hh:Tendsto Y f (𝓝 (hsinc 0)):= (hschi.continuous.tendsto 0).comp (by simpa using (getUp r h).div_const 2); rw [hzero] at hh; have hv:= ((hschi.continuous.tendsto _).comp (h.div_const 2)).div hh one_ne_zero; rw [div_one] at hv; refine hv.congr' ((hh.eventually_ne one_ne_zero).mono fun x hx=>?_); apply (eq_div_iff hx).mpr (_ : plank (M x) ((A x)⁻¹*g x) *_= _) |>.symm; rw [show Y x=_ from rfl, show plank _ _*Y _= _ from plank_g _ (M x) (p x)]; simp only [←mul_assoc,Function.comp_apply,mul_inv_cancel₀ (side_ne _),one_mul]; -- tune
variable {F:X→Momentum}{w: Momentum}(H:Tendsto F f (𝓝 w))
include H
lemma narr : Tendsto (fun i=> narrow (M i) (F i)) f (𝓝 0) := by apply tendsto_pi_nhds.mpr; intro a; exact getUp r (g:=fun i=> F i a) (tendsto_pi_nhds.mp H a)
lemma topple (a:Axis): Tendsto (fun i=> ds (M i) (F i) a) f (𝓝 (w a)) := inward r (tendsto_pi_nhds.mp H a)
lemma minus_T : Tendsto (fun i=> Cminus (M i) (F i)) f (𝓝 2):= by
 have hp: ContinuousAt rad (0:Momentum):= (rad_uniform.choose_spec.choose_spec.2.2.hol 0 (cube_zero _ rad_uniform.choose_spec.choose_spec.1)).continuousAt; have hk:rad (0:Momentum)-kin 0=(2:ℂ):=by norm_num [rad,kin,mag,pl,sine,sqrt]; -- tune
 rw [←hk]; exact ((hp.sub ((show Continuous kin from by unfold kin pl; fun_prop).continuousAt)).tendsto.comp (narr r H))
abbrev pass (w:Momentum):=∑ a:Axis,(w a)^2
lemma feeT: Tendsto (fun i=> D (M i) (F i)) f (𝓝 (pass w/2)):= by
 have he:= minus_T r H; have h2:(2:ℂ)≠0:= two_ne_zero; refine ((tendsto_finsetSum _ (fun i _=> (topple r H i).pow 2)).div he h2).congr' ((he.eventually_ne h2).mono fun i t=> ?_); simp only [Pi.div_apply, ds_sq,mul_div_cancel_right₀ _ (show Cminus (M i) (F i) ≠ 0 from t)]; -- tune
lemma mileL (t:pass w≠0)(a:Axis): Tendsto (fun x=>(A x)⁻¹ * bGraph (narrow (M x) (F x)) a) f (𝓝 (2*w a/pass w)):= by
 let Z:= pass w; have he:= feeT r H; refine Tendsto.congr' (Eventually.of_forall ?_) ((show 2*w a/Z = w a/(Z/2) from (by field_simp)).symm ▸ ((topple r H a).div he (div_ne_zero t two_ne_zero))) -- tune
 intro i; simp only [Pi.div_apply,D,ds,bGraph,div_eq_mul_inv,mul_inv_rev,sq,Pi.smul_apply,smul_eq_mul]; let z:ℂ:= A i; have hp:z≠0:=side_ne _; ring_nf; -- tune
 field_simp
variable (n:ℕ)
def leer(w:Momentum):= ∏ i:Axis,hsinc (w i/2)
include p in
lemma guideM(n:ℕ): Tendsto (fun i=> muff n (M i) (narrow (M i) (F i))) f (𝓝 (leer w ^ n)):= by
 have he(a:Axis): Tendsto (fun i=> plank (M i) ((narrow (M i) (F i)) a)) f (𝓝 (hsinc (w a/2))):= plank_T p r (g:=fun i=>F i a) (tendsto_pi_nhds.mp H a); exact ((tendsto_finsetProd _ fun i _=> he i).pow n)
end
end YM.CF.Window.Largo
