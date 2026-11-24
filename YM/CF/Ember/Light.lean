import YM.CF.Ember.Ray
import YM.CF.Ember.Heap
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
private def plum(a b c z:ℝ):ℝ:= (a^2+c*z+z^2)/(1+b*z+4*z^2)
private def cherry(a b c:ℝ):= c-a^2*b
private def sweet(a b c:ℝ):= 1-4*a^2-b*cherry a b c
private def gum(a b c z:ℝ):= -(4*cherry a b c+b*sweet a b c+4*z*sweet a b c)/(1+b*z+4*z^2)
private lemma sug_a(a b c z) (h:|b| ≤4)(hz:|z|≤1/16): plum a b c z=a^2+z*cherry a b c+z^2*sweet a b c+z^3*gum a b c z:=by
 have hp:|b*z|≤4*(1/16):=by rw [abs_mul]; gcongr
 have ht: 0< 1+b*z+4*z^2:=by nlinarith [(abs_le.mp hp).1]
 let S:= 1+b*z+4*z^2
 change _/S=_+_*(_/S)
 rw [div_eq_iff ht.ne']; simp only [add_mul]; rw [mul_assoc (z^3), div_mul_cancel₀ _ ht.ne']; unfold sweet cherry; ring
private lemma rhub:∃ C:ℝ,0<C∧∀ a b c z :ℝ,|a|≤1→|b|≤4→|c|≤2→|z|≤1/16→ |gum a b c z|≤C:=by
 let S:=Set.Icc (-1:ℝ) 1 ×ˢ (Set.Icc (-4:ℝ) 4 ×ˢ (Set.Icc (-2:ℝ) 2 ×ˢ Set.Icc (-(1/16:ℝ)) (1/16))); have he:IsCompact S:= isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
 let F(v:ℝ×ℝ×ℝ×ℝ):=gum v.1 v.2.1 v.2.2.1 v.2.2.2
 have hv:ContinuousOn F S:=by
   unfold F gum; refine ContinuousOn.div ?_ ?_ ?_
   · apply Continuous.continuousOn; unfold sweet cherry; fun_prop
   · apply Continuous.continuousOn; fun_prop
   rintro ⟨a,b,c,z⟩ h; change 1+b*z+4*z^2≠0; have hb: |b| ≤4:= abs_le.mpr h.2.1; have hx:|z|≤1/16:= abs_le.mpr h.2.2.2; have hh: |b*z|≤4*(1/16):=by rw [abs_mul]; gcongr
   apply ne_of_gt; nlinarith [(abs_le.mp hh).1]
 obtain ⟨C,hC⟩:= he.bddAbove_image hv.abs; exact ⟨max C 1,lt_max_of_lt_right one_pos,fun a b c z ha hb hc hz=> (hC ⟨(a,b,c,z),⟨abs_le.mp ha,abs_le.mp hb,abs_le.mp hc,abs_le.mp hz⟩,rfl⟩).trans (le_max_left ..)⟩
variable {n:Type*}[Fintype n][DecidableEq n]
def harris(T: Op n)(a:Axis)(x:Gaia)(z:ℝ):ℝ:= (oval T (river x) (spark a z)).re
private def w0(x:Gaia)(k:Axis):= x k/‖x‖
private def L(x:Gaia)(k:Axis):= if k=1 then 2*w0 x 1 else 0
private lemma scaleV(T:Op n)(h:star T=T)(a x z)(hp:0<‖x‖):harris T a x z= (32*(Matrix.trace (T*T)).re)/‖x‖^2 *plum (w0 x 1) (4*w0 x a) (L x a) (z/‖x‖):=by
 let t:= z/‖x‖; let c:= 1+4*w0 x a*t+4*t^2; let A:= plum (w0 x 1) (4*w0 x a) (L x a) (z/‖x‖); let R:=‖x‖
 have H : oval T (river x) (spark a z)=(Matrix.trace (T*T))*((32*A/R^2:ℝ):ℂ):=by
    rw [sunray T h]; unfold A plum
    have he : (1+4*w0 x a*(z/R)+4*(z/R)^2)*R^2= R^2+4*z*x a+4*z^2:=by unfold w0 R; field_simp
    have hf:(w0 x 1^2+L x a*(z/R)+(z/R)^2)*(R^2)=x 1^2+z^2+(if a=1 then 2*x 1*z else 0):=by by_cases h:a=1<;> simp [L,h,w0] <;> unfold R <;> field_simp <;> ring
    let Q:= Matrix.trace (T*T)
    change 32*Q*((x 1:ℂ)^2+(z:ℂ)^2+((if a=1 then 2*x 1*z else 0:ℝ):ℂ)) / (((R^2:ℝ):ℂ)*((R^2+4*z*x a+4*z^2:ℝ):ℂ))=_
    rw [←he,show _ + (↑(if a=1 then 2*x 1*z else 0:ℝ):ℂ)=(((w0 x 1^2+L x a*(z/R)+(z/R)^2)*(R^2):ℝ):ℂ) from ?_]; swap; · rw [hf]; push_cast; rfl
    let u :ℂ:= ((w0 x 1^2+L x a*(z/R)+(z/R)^2:ℝ):ℂ); let v:ℂ:= ((1+4*w0 x a*(z/R)+4*(z/R)^2:ℝ):ℂ)
    let r:ℂ:= ((R^2:ℝ):ℂ)
    rw [Complex.ofReal_mul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_div]; change 32*Q*(u*r)/(r*(v*r))=Q*(((32:ℝ):ℂ)* (u/v) /r)
    have hx:r≠0:=by unfold r R; exact_mod_cast (pow_pos hp 2).ne'
    norm_num; by_cases h:v=0; · rw [h]; ring
    field_simp
 unfold harris; rw [H]; simp only [Complex.mul_re,Complex.ofReal_re, Complex.ofReal_im,mul_zero,sub_zero,A,R]; ring

def latticeFieldEstimates(T:Op n)(x:Gaia) : ℝ:=(Matrix.trace (T*T)).re*(16*jetMix x 1 0-16*opJen (springAx 1) x 4+8*opJen (springAx 1) x 2)
lemma aureole (T:Op n)(h:star T=T) : ∃ E:ℝ,0<E∧∀ x:Gaia,∀ z:ℝ, 0<‖x‖→ 0<z→z/‖x‖≤1/16→ ‖((harris T 0 x z+harris T 0 x (-z))-(harris T 1 x z+harris T 1 x (-z)))/(64*z^2)-latticeFieldEstimates T x‖ ≤ E*z/‖x‖^5 :=by
 obtain ⟨C,hc,H⟩:=rhub
 let t:=(Matrix.trace (T*T)).re; let d:=max |t| 1; have hd:0<d:=lt_max_of_lt_right one_pos; refine ⟨2*d*C,by positivity,fun x z hp hx hz=>?_⟩
 let R:=‖x‖; let W i:=w0 x i; let b(a):= 4*W a; let v:=z/R; let Y:=W 1
 have he(a): |W a|≤1:=by unfold W w0; rw [abs_div, abs_of_pos hp,div_le_iff₀ hp, one_mul]; exact (show |x a| ≤ ‖exileE x‖ by change |exileE x a|≤_; exact norm_le_pi_norm _ _ |>.trans' (Real.norm_eq_abs _ |>.symm.le)).trans (orbit_at _)
 have hb(a):|b a|≤4:=by unfold b; rw [abs_mul,abs_of_pos (by norm_num)]; exact mul_le_of_le_one_right (by norm_num) (he a)
 have hu(a):|L x a|≤2:=by
   unfold L; split; · rw [abs_mul,abs_of_pos (by norm_num)]; exact mul_le_of_le_one_right (by norm_num) (he _)
   norm_num
 have hv: |v|≤1/16:=by unfold v R; rw [abs_of_pos (by positivity)]; exact hz
 let Q (a:Axis):= L x a; let G(a u):= gum Y (b a) (Q a) u; let P(a:Axis):= G a v-G a (-v); let K(a:Axis):=sweet Y (b a) (L x a)
 have hg(a:Axis): |P a|≤2*C:=by apply (abs_sub (G a v) (G a (-v))).trans; rw [two_mul]; exact add_le_add (H _ _ _ _ (he _) (hb _) (hu _) hv) (H _ _ _ _ (he _) (hb _) (hu _) (by simpa only [abs_neg] using hv))
 let D:=32*t/R^2
 have hh(a:Axis): harris T a x z+harris T a x (-z)= D*(2*(Y^2+v^2*K a)+v^3*P a):=by
   rw [scaleV T h _ _ _ hp,scaleV T h _ _ _ hp,neg_div]; change D* (plum _ (b a) _ v) + D*plum _ _ _ (-v)=_
   rw [sug_a _ _ _ _ (hb _) hv,sug_a _ _ _ _ (hb _) (show abs (-v) ≤1/16 from by rw [abs_neg]; exact hv)]
   change D*(Y^2+v*_+v^2*K a+v^3* G a v)+D*(_+(-v)*cherry Y (b a) (Q a)+(-v)^2*K a+(-v)^3*G a (-v))=_; unfold P Q K Y; ring
 have hy:t*(K 0-K 1)/R^4=latticeFieldEstimates T x:=by
   unfold latticeFieldEstimates jetMix opJen; simp only [springTouch]; unfold K Y W b L w0 sweet cherry R; norm_num [W,w0,t]; ring
 have hzI: D*(2*v^2*(K 0-K 1))/(64*z^2)=latticeFieldEstimates T x:=by rw [←hy]; unfold D v; field_simp [show R≠0 from hp.ne']; ring
 rw [hh,hh, show (D*_ - D*_)/(64*z^2) = D*(2*v^2*(K 0-K 1))/(64*z^2)+D*(v^3*(P 0-P 1))/(64*z^2) by ring,hzI]; rw [add_sub_cancel_left]; rw [show D*(v^3*(P 0-P 1))/(64*z^2)= t*(P 0-P 1)*(z/(2*R^5)) by unfold D v; field_simp [show R≠0 from hp.ne']; ring]
 have hr: 0<R:=hp; rw [Real.norm_eq_abs, abs_mul,abs_mul,abs_of_pos (by positivity : 0<z/(2*R^5))]; exact (mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left |t| 1) ((abs_sub ..).trans (add_le_add (hg 0) (hg 1))) (abs_nonneg _) hd.le) (by positivity : 0≤z/(2*R^5))).trans_eq (by unfold R d; ring)
lemma sunS (T:Op n): SnowH (latticeFieldEstimates T) ((Matrix.trace (T*T)).re/(12*Real.pi^2)):=by
 constructor
 · intro x hx; unfold latticeFieldEstimates jetMix opJen; have h: ContDiffAt ℝ 1 (fun x:Gaia=> ‖x‖) x:=contDiffAt_id.norm ℝ hx
   have ht:= norm_ne_zero_iff.mpr hx
   simp only [springTouch]; fun_prop (disch:=first|exact pow_ne_zero _ ht|assumption)
 · intro t ht x; unfold latticeFieldEstimates jetMix opJen; simp [real_inner_smul_right, norm_smul, abs_of_pos ht]; field_simp
 intro μ h v
 unfold latticeFieldEstimates; rw [integral_const_mul]
 have hl:= joy_meal h 1 0; have hg:= joy_paid h (springAx 1) 4; have hk:=joy_paid h (springAx 1) 2
 rw [integral_add (f:=fun x=>16*jetMix x 1 0-16*opJen (springAx 1) x 4) ((hl.const_mul 16).sub (hg.const_mul 16)) (hk.const_mul 8), integral_sub (hl.const_mul 16) (hg.const_mul 16),integral_const_mul,integral_const_mul,integral_const_mul]
 change cartWeight*((Matrix.trace (T*T)).re*(16*joyMix μ 1 0-16*joyAx μ (springAx 1) 4+8*joyAx μ (springAx 1) 2))=_
 rw [joy_knot h 1 0 (by decide)]
 rw [joy_two h,joy_heights h 1 0 (by decide),show landX μ=_ from polar_m μ h v]; unfold cartWeight; field_simp; ring
end YM.CF.Ember
