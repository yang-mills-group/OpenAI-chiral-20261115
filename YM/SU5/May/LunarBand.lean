import YM.SU5.May.LunarFrequencies
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Real Complex MeasureTheory AddCircle Lattice
open Window.ArchiveK Window.Largo
open scoped Topology BigOperators ContDiff InnerProductSpace ComplexOrder Interval Classical
variable {T E δ:ℝ}(h:0<T) (q:0<E) (α:ℝ)(p:δ≤1)(u:δ*δ=1)(s:coastE (α*(2* Real.pi))=(δ:ℂ))
def nodeR (T α:ℝ)(n:ℤ):ℝ:= 2*Real.pi/T*((n:ℝ)+α)
private def dampingF(T E:ℝ):ℝ:= Real.exp (-E*T)
noncomputable def earning (T E δ:ℝ):ℝ:= 1-δ*Real.exp (-E*T)
lemma whey_p (b:ℝ):0 ≤ whey E b:=by unfold whey; positivity -- maybe q not included, because denominator zero E=0 and 0/0 ; positivity Lean ok
include h q
include p in
lemma earning_p : 0 < earning T E δ:=by
 unfold earning; rw [sub_pos]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right p (Real.exp_nonneg _)); rw [one_mul, Real.exp_lt_one_iff]; nlinarith
-- universal, arbitrary center.Mith
lemma stableK : Summable fun n:ℤ=> whey E (nodeR T α n) := by
 let B:= 2*π/T; let U(n:ℤ):=(n:ℝ)+α; have ht:0<B:=by unfold B; positivity
 have hv:= (Real.summable_one_div_int_add_rpow α 2).mpr (by norm_num); apply Summable.of_norm_bounded_eventually (hv.mul_left (2/B^2))
 have hm: Set.Finite {n:ℤ|U n=0}:=(show ({n:ℤ|U n=0}:Set ℤ).Subsingleton from fun i x j y=> Int.cast_injective (α:=ℝ) (add_right_cancel (show U i=U j from (show U i=0 from x).trans (show U j=0 from y).symm))).finite -- tune
 filter_upwards [(show ∀ᶠ n in cofinite,U n≠0 from hm.compl_mem_cofinite)] with n e
 rw [Real.norm_of_nonneg (whey_p _)]; change 2/(E^2+(B*U n)^2) ≤ 2/B^2 * (1/|U n|^(2:ℝ)); norm_num; have hh:(U n)^2≠0:= by positivity; 
 calc _ ≤2/(B*U n)^2 := by gcongr; exact le_add_of_nonneg_left (sq_nonneg _)
       _ = _ := by field_simp
include p h q u s
private lemma pir(x:ℝ)(y:coastE x=(δ:ℂ)): coastE (-x)=(δ:ℂ):=by rw [← coast_inv,y,Complex.star_def, Complex.conj_ofReal]
-- unused h etc. tune
private lemma sail_cash(n:ℤ) : coastE (nodeR T α n*T)=(δ:ℂ):=by
 rw [show nodeR T α n*T=2*π*n+α*(2*π) from (by unfold nodeR; field_simp), coast_add,s]
 unfold coastE; rw [show Complex.I*(_ : ℝ)= ↑n*(2*π*Complex.I) from ?_, Complex.exp_int_mul_two_pi_mul_I,one_mul]; push_cast; ring
private lemma exp_receipt (Z b:ℝ)(hz:Z≠0)(y:coastE (b*T)=(δ:ℂ)): (∫ x:ℝ in (-T)..0, coastE (-b*x)*(Real.exp (Z*x):ℂ))=(1-(δ:ℂ)*(Real.exp (-Z*T):ℂ))/((Z:ℂ)-Complex.I*b):=by
 let A:ℂ:= Z-Complex.I*b; have ht:A≠0:=by intro e; apply hz; simpa only [A,sub_re, ofReal_re, I_mul_re,ofReal_im,neg_zero, sub_zero,Complex.zero_re] using congrArg Complex.re e
 have hp(x:ℝ): coastE (-b*x)*(Real.exp (Z*x):ℂ)= Complex.exp (A*x):=by unfold A coastE; push_cast; rw [←Complex.exp_add]; ring_nf
 simp_rw [hp]; rw [integral_exp_mul_complex ht]; rw [← hp (-T)]; rw [neg_mul_neg, y]; simp [neg_mul,A]
-- endpoint & FT
noncomputable def passPos(T α:ℝ):ℝ:= 2*Real.pi/T*α
noncomputable def hood(T E δ x:ℝ):ℂ:= (Real.exp (E*x):ℂ)+(δ:ℂ)*(Real.exp (-E*T):ℂ)*(Real.exp (-E*x):ℂ)
def sheaf(T E δ α x:ℝ):ℂ:= coastE (-passPos T α *x) * hood T E δ x
-- permit negative interval
omit p q
private lemma hood_edge : sheaf T E δ α (-T)=sheaf T E δ α 0:=by
 unfold sheaf hood; rw [neg_mul_neg, show coastE (_:ℝ)= ↑δ from ?_]; swap; · rw [show passPos T α*T=α*(2*π) from (by unfold passPos; field_simp),s]
 rw [neg_mul_neg]; simp only [mul_zero, Real.exp_zero, coast_zero,ofReal_one,mul_one,one_mul]
 let Y:= (Real.exp (-E*T):ℂ); rw [mul_neg E, ← neg_mul E]; have he: Y*((Real.exp (E*T):ℝ):ℂ)=1:=by unfold Y; rw [←ofReal_mul,←Real.exp_add]; simp
 have hx: (δ:ℂ) * (δ:ℂ) =1:=by exact_mod_cast u
 change (↑δ:ℂ)*(Y+ ↑δ*Y*↑(_))=_; unfold Y at he; -- try
 rw [mul_add,mul_assoc (δ:ℂ) _, he] -- fails Y motif tune
 simp only [mul_one,hx]; exact add_comm ..
include p q u
local notation "V" n:max => nodeR T α n
omit p q h u s in
private lemma coaste' (n:ℤ)(x:ℝ): fourier (T:=T) n (↑x:AddCircle T) = coastE ((2*Real.pi/T*n)*x):=by
 rw [fourier_coe_apply]; unfold coastE; push_cast; ring_nf -- arg 'ScopeHT
private lemma integrate (n:ℤ): (∫ x:ℝ in (-T)..0, fourier (-n) (↑x:AddCircle T) * sheaf T E δ α x) =↑(E * earning T E δ * whey E (nodeR T α n)):=by
 let b:= V n; let Y:= Real.exp (-E*T); let c:=δ*Y; let f(Z x:ℝ):= coastE (-b*x)*(Real.exp (Z*x):ℂ); have hF(Z:ℝ):IntervalIntegrable (f Z) volume (-T) 0 := Continuous.intervalIntegrable (by unfold f; fun_prop) _ _
 have hp(x:ℝ): fourier (-n) (↑x:AddCircle T)*sheaf T E δ α x=f E x+(c:ℂ)*f (-E) x:=by
    unfold sheaf; rw [coaste',←mul_assoc,←coast_add, show (2*π/T)*↑(-n)*x + -passPos T α*x = -b*x from (by unfold b nodeR passPos; push_cast; ring)]; unfold f c Y hood; push_cast; ring -- sign argument
 simp_rw [hp]; rw [intervalIntegral.integral_add (hF E) ((hF (-E)).const_mul _), intervalIntegral.integral_const_mul]; unfold f; let hb:= sail_cash h q α p u s n -- adjust
 rw [exp_receipt h q α p u s E b q.ne' hb,exp_receipt h q α p u s (-E) b (neg_ne_zero.mpr q.ne') hb] -- adjust
 have he:earning T E δ=1-c:=rfl; rw [he]; change _=(↑(E*(1-c)*(2/(E^2+b^2)):ℝ):ℂ); simp only [ofReal_mul, neg_neg,ofReal_add,ofReal_one,ofReal_sub,ofReal_div,ofReal_ofNat,ofReal_pow,ofReal_neg]; have e:E^2+b^2≠0:=by positivity
 let B0:=((E:ℂ)-Complex.I*b); let B1:=(-(E:ℂ)-Complex.I*b); have h₀:B0≠0:=fun i=> q.ne' (by simpa [B0] using congrArg Complex.re i); have h₁:B1 ≠0:=fun i=> q.ne' (by simpa [B1] using congrArg Complex.re i); have H:(E:ℂ)^2+ (b:ℂ)^2= -(B0*B1):=by unfold B0 B1; ring_nf; simp
 rw [H]; let C':ℂ:=δ; let Θ':ℂ:=Real.exp (E*T); have Y': (Y:ℂ)*Θ'=1:= by unfold Y Θ'; rw [← ofReal_mul,←Real.exp_add]; simp
 have Z0:(δ:ℂ)*(δ:ℂ)=1:=by exact_mod_cast u
 have h2: (c:ℂ)*(1-(δ:ℂ)*Θ') = - (1-(c:ℂ)) := by unfold c; push_cast at *; linear_combination - ((Y:ℂ)*Θ')*Z0-Y'
 -- maybe push_cast converts Real.exp (!) definally strong? inspect
 change (1-(δ:ℂ)* (Y:ℂ))/B0+((c:ℂ) * ((1-(δ:ℂ)*Θ')/B1))=_ -- simp only introduced too much! inspect
 rw [← mul_div_assoc,h2, show (δ:ℂ)*(Y:ℂ)=(c:ℂ) from (ofReal_mul ..).symm]; field_simp
 unfold B0 B1; ring
#print axioms integrate
noncomputable def fareP (T E δ:ℝ):ℝ:= T/(E*earning T E δ)
lemma loomP(x:ℝ)(v:-T<x)(w:x<0): HasSum (fun n:ℤ=> coastE (x* V n)* (whey E (V n):ℂ)) ((fareP T E δ:ℂ)*hood T E δ x):=by
 letI : Fact (0<T):= ⟨h⟩; let Y:= sheaf T E δ α; let f :=AddCircle.liftIoc T (-T) Y; let C:= coastE (passPos T α*x); let H:=earning T E δ; have he:0<H:= earning_p h q p; let F:= fareP T E δ; let U:ℝ:= E*H; have hU:U≠0:= (mul_pos q he).ne'; have hV: Continuous Y:=by unfold Y sheaf hood; fun_prop
 let g:C(AddCircle T,ℂ):=⟨f,liftIoc_continuous (by rw [neg_add_cancel]; exact hood_edge h α u s) hV.continuousOn⟩ -- notation collision
 have hp(x:ℝ)(p:-T < x)(v:x ≤ 0): g ↑x=Y x:=by change f ↑x=_; exact liftIoc_coe_apply (by rw [neg_add_cancel]; exact ⟨p,v⟩)
 have hv(x:ℝ)(p:-T ≤ x)(v:x ≤ 0):g ↑x=Y x:=by
    rcases lt_or_eq_of_le p with p|rfl; exact hp x p v; have hv:= coe_add_period T (-T); rw [neg_add_cancel] at hv; rw [←hv,hp _ (neg_neg_of_pos h) le_rfl]; exact (hood_edge h α u s).symm
 have hm(n:ℤ): fourierCoeff g n=((1/T * U:ℝ):ℂ)*(whey E (nodeR T α n):ℂ) := by
    rw [fourierCoeff_eq_intervalIntegral _ _ (-T), neg_add_cancel,Complex.real_smul]; have hx: -T≤0:=by linarith
    push_cast; rw [mul_assoc]; refine congrArg (fun z:ℂ=> ((1/(T:ℂ)):ℂ)* z) (Eq.trans (intervalIntegral.integral_congr (g:=fun x:ℝ=> fourier (-n) (↑x:AddCircle T)* sheaf T E δ α x) ?_) ?_)
    · intro i p; rw [Set.uIcc_of_le hx] at p; simp only [smul_eq_mul,hv i p.1 p.2]; rfl -- goal RHS gap likely metavar
    rw [integrate h q α p u s]; unfold U H; push_cast; rfl -- maybe mismatch F.value?
 have hZ: Summable (fourierCoeff g):=by rw [funext hm]; exact (Complex.summable_ofReal.mpr (stableK h q α)).mul_left _
 have K:= has_pointwise_sum_fourier_series_of_summable hZ (↑x:AddCircle T); rw [hp _ v w.le] at K
 have hδ:C * Y x= hood T E δ x:= by unfold C Y sheaf; rw [←mul_assoc,←coast_add]; ring_nf; simp -- tune
 rw [←hδ,←mul_assoc]; refine ((K.mul_left ((F:ℂ)*C))).congr_fun ?_
 intro n; rw [hm, coaste',smul_eq_mul]; have hx: C*coastE (2*π/T*↑n*x)=coastE (x* V n):=by unfold C nodeR; rw [←coast_add]; unfold passPos; ring_nf
 rw [← hx]; have hg:(F:ℂ)* ((1/T*U:ℝ):ℂ)=1:=by rw [←ofReal_mul,show F*_=1 from ?_]; rfl; change T/U*_= _; field_simp
 linear_combination - ((C* (whey E (nodeR T α n):ℂ))*coastE (2*π/T*↑n*x)) * hg
#print axioms loomP
end YM.CF.May.Lunar
