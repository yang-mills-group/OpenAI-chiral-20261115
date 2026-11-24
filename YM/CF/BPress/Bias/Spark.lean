import YM.CF.BPress.Bias.Meridian
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter Lattice Laurent Bloch Next.Free Fir Lat Spin Cube
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
-- two momenta relate by reflection: high θ/n modes choose by arithmetic
variable {N: Side} {w:ℝ}{k l: Site N}
structure Reflection (w:ℝ)(k l:Site N):Prop where
 left:pm k axisR=w
 right:pm l axisR=-w
 mirror(i:Axis)(p:i≠axisR):k i=l i
 safe (i:Axis)(u:i≠0):|pm k i| ≤ w
namespace Reflection
variable (M:Jill.Male)(p:Reflection w k l)(j:ℕ)
include p
local notation "r(" k ")"=>pm k 0
lemma flux(i:Axis):|pm k i|=|pm l i|:=by
   by_cases h:i=axisR; · rw [h,p.left,p.right,abs_neg]
   unfold pm; rw [Function.comp_apply,Function.comp_apply,p.mirror i h]; -- indent
lemma clock: r(k)=r(l):=congrArg Lat.principal (p.mirror 0 (by decide))
lemma level {t:ℝ}(h:w ≤ t)(e: |r(k)|≤t): ‖Rush.mel k‖≤t ∧ ‖Rush.mel l‖≤t:=by
 have hu (i:Axis): |pm k i|≤t:=by
   by_cases hi:i=0; · rwa [hi]
   exact (p.safe i hi).trans h
 have ht:= (abs_nonneg _).trans e; exact ⟨(pi_norm_le_iff_of_nonneg ht).mpr (fun i=>by rw [pm_norm]; exact hu i),(pi_norm_le_iff_of_nonneg ht).mpr (fun i=>by rw [pm_norm,←p.flux]; exact hu i) ⟩
lemma apart (h:0≤w) : ‖Rush.mel k-Rush.mel l‖≤2*w:=by
 refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>?_); unfold Rush.mel tmap; rw [Pi.sub_apply,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; by_cases hi:i=axisR; · rw [hi,p.left,p.right,sub_neg_eq_add,←two_mul,abs_of_nonneg (by positivity)];
 unfold pm; rw [Function.comp_apply,Function.comp_apply,p.mirror i hi]; simp [h]
omit p in
abbrev drag (M:Jill.Male)(w:ℝ):=(M.val.val:ℝ)*Real.sin (w/M.val.val)
omit p in
abbrev pulse (j:ℕ)(M:Jill.Male)(w:ℝ)(k: Site N):= biasR j M k * drag M w / clockS M.val k
omit p in
lemma heart (h:0<w)(s:w≤1) : w/2≤ drag M w ∧ drag M w ≤w:=by
 unfold drag; have H:= nPos M.val; let a:ℝ:= M.val.val; let x:=w/a; have he:0<x:=div_pos h H; have ha:1≤(M.val.val:ℝ):= Nat.one_le_cast.mpr M.val.property; have hx:x≤1:=by unfold x a; rw [div_le_iff₀ H]; linarith
 have hz:x^3 ≤ x:=by nlinarith [mul_nonneg he.le (sub_nonneg.mpr (calc x^2 ≤ 1^2 := pow_le_pow_left₀ he.le hx 2))]
 rw [show w/2=M.val.val*(x/2) by unfold x a; field_simp]; exact ⟨mul_le_mul_of_nonneg_left (by linarith [Real.sin_ge_sub_cube he.le]) H.le,(mul_le_mul_of_nonneg_left (Real.sin_le he.le) H.le).trans_eq (mul_div_cancel₀ _ H.ne')⟩
abbrev A (j:ℕ)(M:Jill.Male)(k:Site N):= mixL j M.val (Rush.mel k) axisR
lemma glide : A j M k-A j M l = ((pulse j M w k+pulse j M w l:ℝ):ℂ)+(extras j M.val (Rush.mel k) axisR-extras j M.val (Rush.mel l) axisR):=by
 unfold A; rw [mix_com,mix_com]; simp only [Pi.add_apply,Pi.smul_apply, bloom_real _ j k,bloom_real _ j l,D_real k, D_real l, ds_value,smul_eq_mul, p.left,p.right]; unfold pulse drag; push_cast; rw [neg_div,Complex.sin_neg]; ring_nf
omit p in
lemma pulse_far {r d C:ℝ} (w₀:0<w)(s:w≤1)(a:0<r)(v:0<d) (u:d*r^2≤clockS M.val k) (e:|biasR j M k|≤C): |pulse j M w k| ≤ C/(d*r^2)*w:=by
 obtain ⟨c,h⟩:= heart M w₀ s; unfold pulse; have p:0<d*r^2:=by positivity
 have:= (abs_nonneg _).trans e; have:= (half_pos w₀).trans_le c; rw [abs_div,abs_mul,abs_of_pos (p.trans_le u),abs_of_pos ((half_pos w₀).trans_le c),div_mul_eq_mul_div]; gcongr
omit p in
lemma pulse_near {δ:ℝ} (wt:0<w)(s:w≤1)(a:0<δ)(p:0<clockS M.val k) (u:clockS M.val k≤ 4*δ^2) (e:1/2≤biasR j M k): w/(16*δ^2)≤ pulse j M w k:=by
 obtain ⟨c,_⟩:=heart M wt s; rw [show w/(16*δ^2)=(1/2*(w/2))/(4*δ^2) by ring]; unfold pulse; have he:0< drag M w:=(half_pos wt).trans_le c; have h:= one_half_pos.trans_le e; gcongr
end Reflection
variable {τ:ℝ} {j:ℕ} (h:1≤j)
open Reflection
lemma neg_real (x:ℂ): -‖x‖≤x.re:= (abs_le.mp (Complex.abs_re_le_norm x)).1
include h in
lemma reflectionSpark (T:ℝ) (hT:0≤T): ∃ η C:ℝ,0<η ∧ 0<C ∧ ∀ (M:Jill.Male)(τ:ℝ), |τ|≤T → ∀ (w:ℝ),0<w→w≤η→∀ (N:Side)(k l : Site N), Reflection w k l→ -(C*w)+(if |pm k 0| ≤ w then 1/(16*w) else 0) ≤ (Complex.exp (((pm k 0 * τ:ℝ):ℂ)*Complex.I)*(A j M k-A j M l)).re:=by
 obtain ⟨r,R,a,S,p⟩:=bloom_geometry j; obtain ⟨d,v,hp⟩:= D_angle; obtain ⟨s,u,g⟩:=D_surface; obtain ⟨L,hL,H⟩:=moderateSlope (extras_pay j h (·.val) (fun i=>i.property) axisR)
 let η:=min (min r s) (1/(2*(1+T))); have h₀:0<η:=lt_min (lt_min a u) (by positivity); have hη: η≤1/(2*(1+T)):=min_le_right ..; let J:= R/(d*η^2); have hl:0<J:= div_pos S (by positivity)
 refine ⟨η,2*J+2*L,h₀,by positivity,fun M τ y w e f N k l kL=>?_⟩; have hw: w≤1:=f.trans (hη.trans (by rw [div_le_one (by positivity)]; linarith)); rw [kL.glide M j,mul_add,Complex.add_re]; let r':= pm k 0; let ϕ:= Complex.exp (((r'*τ:ℝ):ℂ)*Complex.I); have hv:‖ϕ‖=1:=Complex.norm_exp_ofReal_mul_I _; let E(x:Site N):=extras j M.val (Rush.mel x) axisR; have hy: -(L*2*w)≤ (ϕ*(E k-E l)).re:=by
    apply le_trans ?_ (neg_real _); rw [norm_mul,hv,one_mul]; apply neg_le_neg; rw [mul_assoc]; exact (H _ _ (Rush.mel_h _) _ (Rush.mel_h _)).trans (mul_le_mul_of_nonneg_left (kL.apart e.le) hL.le)
 rw [Complex.mul_re]; change _ ≤ ϕ.re * _ - ϕ.im * _ + (ϕ*(E k-E l)).re; rw [Complex.ofReal_re,Complex.ofReal_im, mul_zero, sub_zero]
 let U := @pulse N j M w; by_cases t:|r'| ≤ η; swap
 · push Not at t; rw [if_neg (not_le.mpr (f.trans_lt t))]; have hg: (J*w)>0:=mul_pos hl e; have ht:η < |pm l 0|:=by rw [← kL.clock]; exact t
   have hu (x:Site N)(x0:η < |pm x 0|): |U x|≤ J*w:=pulse_far M j e hw h₀ v (hp _ _ _ _ h₀.le (x0.le.trans (by rw [← pm_norm]; exact norm_le_pi_norm ..))) (p M N x).1
   have hk:= calc
     |ϕ.re*(U k+U l)| ≤ |U k|+|U l|:=by rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hv ▸ Complex.abs_re_le_norm _)).trans (abs_add_le ..)
     _ ≤ _:= add_le_add (hu k t) (hu l ht)
   unfold U at hk; linarith [(abs_le.mp hk).1]
 have hz:|r'| * |τ| ≤ 1:= by apply (mul_le_mul t y (abs_nonneg _) h₀.le).trans; apply (mul_le_mul_of_nonneg_right hη hT).trans; rw [div_mul_eq_mul_div,div_le_one (by positivity)]; linarith
 have he:1/2 ≤ ϕ.re:=by
   unfold ϕ; rw [Complex.exp_mul_I]; simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]; rw [Complex.add_re,Complex.mul_re]; have ht:= Real.abs_cos_sub_cos_le (r'*τ) 0; have hh: (r'*τ)^2 ≤ 1:=by rw [←sq_abs,abs_mul]; exact (pow_le_pow_left₀ (mul_nonneg (abs_nonneg r') (abs_nonneg τ)) hz 2).trans_eq (one_pow _)
   simp only [Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]; linarith [Real.one_sub_sq_div_two_le_cos (x:=r'*τ)]
 have hGt(x:Site N)(z:ℝ)(ez:0<z)(fz:z≤η)(y:‖Rush.mel x‖≤z): w/(16*z^2)≤ U x:=by
    have hx:= (le_trans y fz); have ht:η≤min r s:= min_le_left _ _; have hz:= (g M N x (hx.trans (ht.trans (min_le_right r s)))); exact pulse_near M j e hw ez (noGhost _ (base_subset_realCube zone_pos (Rush.mel_h x)) (Rush.mel_away x)) (hz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) y 2) (by norm_num))) ((p M N x).2 (hx.trans (ht.trans (min_le_left r s))))
 have U_le (z:ℝ)(hz:w≤z)(hr':|r'|≤z)(tz:z≤η): w/(16*z^2) ≤ ϕ.re*(U k+U l):=by
   have et:= e.trans_le hz; obtain ⟨hp,hq⟩:= kL.level hz hr'; exact le_trans (le_of_eq (show w/(16*z^2)=1/2*(w/(16*z^2)+w/(16*z^2)) by ring)) (mul_le_mul he (add_le_add (hGt _ z et tz hp) (hGt _ z et tz hq)) (by positivity) (by linarith))
 split; next hx=> have hg:= U_le w le_rfl hx f; change w/(16*w^2) ≤ _*(pulse j M w k + pulse j M w l) at hg; rw [show w/(16*w^2)=1/(16*w) by field_simp] at hg; nlinarith
 next hx=> have hg:= U_le η f t le_rfl; unfold U at hg; nlinarith [show 0<w/(16*η^2) by positivity]
end YM.CF.BPress.Bias
