import YM.SU5.Reconstruction.Marque.Studio
import Mathlib.Analysis.SpecialFunctions.Complex.Log
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Matrix Real Complex
open scoped Matrix MatrixGroups Topology Classical
noncomputable def rich (v:ℝ) : ℂˣ:= Units.mk0 _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne')
noncomputable def GUnit (v:ℝ) : ℂˣ:= Units.mk0 (Complex.exp (↑v * Complex.I)) (Complex.exp_ne_zero _)
@[simp] lemma rich_val(v:ℝ): (rich v:ℂ)= ↑(Real.exp v):=rfl
@[simp] lemma G_val(v:ℝ): (GUnit v:ℂ)= Complex.exp (↑v * Complex.I):=rfl
variable (v:ℝ)
@[simp] lemma rich_one:rich 0=1:= by ext1; simp
@[simp] lemma G_start:GUnit 0=1:= by ext1; simp
lemma rich_add(w:ℝ): rich (v+w)=rich v * rich w:= by ext1; simp[Real.exp_add]
lemma G_add(w:ℝ): GUnit (v+w)=GUnit v*GUnit w:= by ext1; simp only [G_val,ofReal_add,Units.val_mul, add_mul,Complex.exp_add]
@[fun_prop] lemma rich_cont:Continuous rich:=Units.continuous_iff.mpr ⟨show Continuous (fun v:ℝ=> ((Real.exp v:ℝ):ℂ)) by fun_prop,by simp only [Units.val_inv_eq_inv_val,rich_val]; fun_prop (disch:=simp [(Real.exp_pos _).ne'])⟩ -- tune
@[fun_prop] lemma G_cont:Continuous GUnit:= Units.continuous_iff.mpr ⟨show Continuous (fun v:ℝ=> Complex.exp (↑v*Complex.I)) by fun_prop,by simp only [Units.val_inv_eq_inv_val,G_val]; fun_prop (disch:=simp)⟩
noncomputable def Tuning := Pole (rich v)
noncomputable def Tope (p:ℂˣ):Two:=
 pin (Real.cosh v) ((p:ℂ)*(Real.sinh v)) ((p:ℂ)⁻¹*(Real.sinh v)) (Real.cosh v) (by
   have he := p.ne_zero
   have ht: (↑(Real.cosh v):ℂ)^2 - (↑(Real.sinh v):ℂ)^2=1:= by exact_mod_cast Real.cosh_sq_sub_sinh_sq v
   field_simp; linear_combination ht)
noncomputable def Zip(v:ℝ):Two:=Tope v 1
noncomputable def Yell(v:ℝ):Two:= Tope v (Units.mk0 _ I_ne_zero)
variable (p:ℂˣ)
@[simp] lemma tuning_one:Tuning 0=1:= by simp [Tuning]
@[simp] lemma tope_one:Tope 0 p=1:=by apply tone <;> simp [Tope]
lemma tuning_add(w:ℝ):Tuning (v+w)=Tuning v*Tuning w:=by simp[Tuning, rich_add]
lemma tope_add(w:ℝ):Tope (v+w) p=Tope v p * Tope w p:=by apply tone <;> (simp [Tope, Real.cosh_add, Real.sinh_add] <;> field_simp <;> ring)
@[fun_prop] lemma tun_cont:Continuous Tuning:=by unfold Tuning; fun_prop
@[fun_prop] lemma tope_cont:Continuous (fun v=> Tope v p):= by refine fromFour _ _ _ _ _ ?_ ?_ ?_ ?_; all_goals fun_prop -- fails
-- positive Pole routes & spins
lemma crossElem(a:ℝ)(ha:0<a): ∃ v:ℝ, (rich v:ℂ)=(a:ℂ):= ⟨Real.log a,by simp[Real.exp_log ha]⟩
lemma Head_scale(t:ℝ):rehome (Tuning v) (Head ((p:ℂ) * (t:ℂ)))= Head ((p:ℂ)* ((Real.exp (2*v)*t:ℝ):ℂ)):= by
 rw[Tuning, scales,rich_val, show 2*v=v+v by ring, Real.exp_add]; push_cast; congr 1; ring
-- produce a pure head.Lift when t real
lemma craft : ∃ (s:ℝ),0<s ∧ ∀ u:ℂˣ,∃ a b c d:ℝ, Tope a u*Tuning b* Tope c u*Tuning d= Head ((u:ℂ) *(s:ℂ)):= by
 -- choose cosh a, sinh a; left positive? WANT upper positive; a negative. choose sinh c / cosh c = e.g.4/9, k=2, tanh a=-1/9.
 let t:ℝ:=1/2; let a:= Real.artanh (-t/4); let c:=Real.artanh t
 let y:= Real.cosh a; let z:= Real.cosh c; let w:=Real.sinh c
 have eq: w=t*z:= (div_eq_iff (Real.cosh_pos c).ne').mp ((Real.tanh_eq_sinh_div_cosh _).symm.trans (Real.tanh_artanh (show t∈Ioo (-1:ℝ) 1 by dsimp[t]; constructor <;> norm_num))) -- defeq tanh?
 have eh: Real.sinh a= (-t/4)*y:= (div_eq_iff (Real.cosh_pos a).ne').mp ((Real.tanh_eq_sinh_div_cosh _).symm.trans (Real.tanh_artanh (show -t/4∈Ioo (-1:ℝ) 1 by dsimp [t]; constructor<;> norm_num)))
 have hy:0<y:= Real.cosh_pos a; have hz:0<z:= Real.cosh_pos c; have ht:0<t:= by unfold t; norm_num
 -- diag A=2*y*z + (-ty/4)*(tz)/2= y*z*(2- t²/8). B/(p) = 2*y*tz + - t*y*z/8. multiply by [1/m,m]
 let m:=y*z*(2-t^2/8)
 let r:= y*z*t*(2-1/8)
 have hp:0<(2-t^2/8:ℝ):=by dsimp[t]; norm_num
 have hm:0<m:=by unfold m; positivity
 obtain ⟨b,hb⟩:=crossElem 2 zero_lt_two
 obtain ⟨d,hd⟩:=crossElem m⁻¹ (inv_pos.mpr hm)
 have m':(m:ℂ)≠0:=by exact_mod_cast hm.ne'
 have hb':(rich b:ℂ)=2:=by simpa only [ofReal_ofNat] using hb
 rw [ofReal_inv] at hd
 refine ⟨r*m,by dsimp [r]; positivity,fun u=>?_⟩
 let G:=Tope a u*Tuning b* Tope c u; have e:B G=(u:ℂ)*(r:ℂ):= by
    simp only [G,B_mul,A_mul,Tope,Tuning,Pole,hb',Ap,Bp,Cp,Dp,r,eh, show Real.sinh c=t*z from eq]; unfold y z; push_cast; ring
 have v:C G=0:=by
    simp only [G,D_mul,C_mul,Tope,Tuning,Pole,hb',Ap,Bp,Cp,Dp,eh,show Real.sinh c=t*z from eq]; unfold y z; push_cast; ring
 have f:A G=(m:ℂ):=by
    simp only [G, A_mul,B_mul,Tope,Tuning,Pole,hb',Ap,Bp,Cp,Dp,eh,show Real.sinh c=t*z from eq,m];unfold y z; push_cast; field_simp; ring
 let K:=G*Tuning d; have hk:A K=1:=by simp only [K,Tuning,A_mul,Pole,hd,f,Ap,Cp,mul_zero,add_zero,mul_inv_cancel₀ m'];
 have hk':C K=0:= by simp [K,Tuning,Pole,v];
 refine ⟨a,b,c,d,tone K _ (by rw[hk];rfl) (by simp only [K,Tuning,B_mul,Pole,Bp,Dp,e,hd,mul_zero,inv_inv,zero_add,Head]; push_cast; ring) (by rw [hk'];rfl) ?_⟩
 have p:=det K; rw[hk,hk'] at p; simpa [Head] using p
lemma reversedTail(v t:ℝ) : rehome (Tuning v) (Tail ((p:ℂ)*(t:ℂ)))=Tail ((p:ℂ) *((Real.exp (- (2*v))*t:ℝ):ℂ)):= by
 apply tone <;> (simp [rehome,Tuning,Pole,Tail,show - (2*v)= -v+ -v by ring,Real.exp_add,Real.exp_neg] <;> ring)
-- transpose flip Tope invert? lemma
lemma carriesTail {b a c d:ℝ}{t:ℂ}(h: Tope a p*Tuning b*Tope c p*Tuning d=Head t):Tuning d * (Tope c p⁻¹ * (Tuning b * Tope a p⁻¹))=Tail t:=by
 let G:Two→Two:= SpecialLinearGroup.transpose
 have he(u v:Two):G (u*v)=G v*G u:= Subtype.ext (transpose_mul u.1 v.1)
 have hx(w:ℝ):G (Tope w p)= Tope w p⁻¹:=by apply tone <;> first | rfl | simp [A,B,C,D,val,Tope,pin,G,Matrix.SpecialLinearGroup.transpose]
 have hp(w:ℝ): G (Tuning w)=Tuning w:=tone _ _ rfl rfl rfl rfl
 rw [← hx,← hx,← hp b]; nth_rw 1 [← hp d]; rw [← he,← he,← he,h]; exact tone _ _ rfl rfl rfl rfl

lemma heel (p:ℂˣ)(t:ℝ) : Tope t (-p)=Tope (-t) p:= by apply tone <;> simp[Tope]
-- circuit generation for later
lemma ru (t:ℂˣ): Head (t:ℂ)* Tail (-(t:ℂ)⁻¹)*Head (t:ℂ)=Pole t* turn:= by apply tone <;> simp [Head,Tail,Pole,turn]
lemma menar (g:Two)(p:A g≠0): g=Tail (C g/A g)* Pole (Units.mk0 _ p) * Head (B g/A g):= by
 apply tone <;> simp [Head,Tail,Pole,p]; all_goals field_simp; try (first|(solve|ring)|linear_combination det g) -- tune
-- very compact chart at offdiag B or C, avoid unit continu
lemma pad (g:Two)(p:B g ≠0): g=Tail ((D g-1)/B g)* Head (B g) * Tail ((A g-1)/ B g):= by
 apply tone <;> simp[Head,Tail] <;> field_simp <;> first|(solve|ring)|linear_combination -det g
lemma padded : ∀ g:Two,∃ w, B (g*Head w)≠0:= by
 intro g; by_cases e:B g=0; refine ⟨1,?_⟩; simp [Head,e]; exact left_ne_zero_of_mul_eq_one (show A g*D g=1 by simpa [e] using det g); exact ⟨0,by simpa using e⟩
end YM.Marque
