import YM.SU5.FiniteGaugeData.Crest.Spline
import YM.CF.Fir.Marin
import YM.CF.Onyx.Gold
/-! # Temporal Hankel after regulator removal for the paired grant
    geometry first. DIP infinite rank after Large-Male, need not at any single Male.
    Limit symbol and isolated rates compile in subsequent papers. Here aliases still individual.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Shore
open Function Filter Topology NormedSpace Metric Set Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I

private lemma height_side : Tendsto (fun n:Side=>n.val) atTop atTop:= tendsto_atTop.mpr (fun b=> ((eventually_ge_atTop (⟨b+1,by omega⟩:Side)).mono (fun x (p:b+1 ≤ x.val)=> Nat.le_of_succ_le p)))
private def twistMark:=dslope chip 0
private lemma twistCont : Continuous twistMark:= by
 apply continuous_iff_continuousAt.mpr; intro z; by_cases h:z=0
 · subst z; apply continuousAt_dslope_same.mpr; unfold chip; fun_prop
 apply (continuousAt_dslope_of_ne h).mpr; unfold chip; fun_prop
private lemma twistZero : twistMark 0=I:=by
 simp only [twistMark,dslope_same]; refine HasDerivAt.deriv ?_; convert ((hasDerivAt_id' (0:ℂ)).const_mul I).cexp.sub_const 1 using 1; · rfl -- tune
 · simp
private lemma turning (L:Side)(u:ℂ) : let M:ℂ:=L.val; rail L (u/M)*twistMark (u/M)=twistMark u:=by
 intro M; by_cases p:u=0
 · subst u; simp
 have hp : M≠0:= side_ne _; unfold twistMark; rw [dslope_of_ne _ p,dslope_of_ne _ (div_ne_zero p hp)]; simp only [slope_def_field,sub_zero,chip_origin]
 let z:=u/M; have hk:= rail_chip L z; change M*rail L z*chip z=chip (M*z) at hk; rw [show M*z=u by unfold z; field_simp] at hk; rw [←hk]; unfold z; field_simp [p,hp]
variable {ι:Type*}{l:Filter ι}{M:ι→Side}(v:Tendsto M l atTop) {u:ι→ℂ} {p:ℂ} (e:Tendsto u l (𝓝 p))
include v
lemma thinning : Tendsto (fun i=> ((↑(M i).val:ℂ))⁻¹ ) l (𝓝 0):=by
 simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (height_side.comp v))) -- context synth?
local notation "γ" i:max=> ↑(M i).val
local notation "Φ" i:max=> u i/γ i
include e
private lemma melts : Tendsto (fun i=>Φ i) l (𝓝 0):=by simpa only [div_eq_mul_inv,mul_zero] using e.mul (thinning v)
private lemma rail_turn : Tendsto (fun i=>rail (M i) (Φ i)) l (𝓝 (twistMark p/I)):=by
 have he : Tendsto (fun i=>twistMark (Φ i)) l (𝓝 I) := twistZero ▸ ((twistCont.tendsto 0).comp (melts v e))
 refine Tendsto.congr' ?_ (((twistCont.tendsto p).comp e).div he (by simp))
 filter_upwards [he.eventually (eventually_ne_nhds Complex.I_ne_zero)] with i w; exact ((eq_div_iff w).mpr (turning (M i) (u i))).symm
private lemma spins_down (w:∀ᶠ i in l, Odd (M i).val): Tendsto (fun i=>twirl (Φ i) (-Next.Free.mid (M i))) l (𝓝 (Complex.exp (-((1:ℂ)/2)*(I*p)))):=by
 have H : Tendsto (fun i=> (((1:ℂ)-(γ i:ℂ)⁻¹)/2)) l (𝓝 (1/2)):=by simpa only [sub_zero] using (tendsto_const_nhds.sub (thinning v)).div_const 2
 refine ((Complex.continuous_exp.tendsto _).comp (H.neg.mul (e.const_mul I))).congr' ?_
 filter_upwards [w] with i p; have hk : 2* ((Next.Free.mid (M i)):ℂ) + 1= (γ i:ℂ):= by exact_mod_cast mid_double (M i) p
 have ht:= side_ne (M i); simp only [twirl,Function.comp_apply,Int.cast_neg]; congr 1; field_simp; linear_combination hk*(u i) -- signs

omit e v
private lemma normalized (x:ℝ):Complex.exp (-((1:ℂ)/2)*(I*x))*(twistMark x/I)=skirt x:=by
 by_cases t:x=0
 · subst x; simp [twistZero,skirt]
 have hp:(x:ℂ)≠0:=by exact_mod_cast t
 let a:=surge (1/2:ℝ) x; let b:=surge (-(1/2:ℝ)) x
 have hb : b=Complex.exp (-((1:ℂ)/2)*(I*x)):=by unfold b surge; push_cast; ring_nf
 have he : b* Complex.exp (I*x)=a:=by rw [hb, ←Complex.exp_add]; unfold a surge; push_cast; ring_nf
 have ht:= step_sinc x; have hg : b*chip ↑x=a-b:=by unfold chip; rw [mul_sub,he,mul_one]
 unfold twistMark; rw [←hb,dslope_of_ne _ hp,slope_def_field]; simp only [sub_zero,chip_origin]; rw [← mul_div_assoc, ←mul_div_assoc,hg]; field_simp; change -(I*x)*skirt x= -(a-b) at ht; linear_combination ht -- fix
include e v
lemma plank_c (w:∀ᶠ i in l,Odd (M i).val) (x:ℝ)(hz:p=x): Tendsto (fun i=> plank (M i) (Φ i)) l (𝓝 (skirt x)):=by subst p; rw [←normalized x]; exact (spins_down v e w).mul (rail_turn v e)

include v
omit e
local notation "△" w=>∑ i:Axis,(w i)^2
def radius (z:Bin) :ℝ:=∑ i:Axis,z i^2
omit v in
lemma radius_pos(z:Bin)(p:z≠0):0<radius z:=by classical
 obtain ⟨x,h⟩:= Function.ne_iff.mp p; change z x≠0 at h
 exact lt_of_lt_of_le (sq_pos_of_ne_zero h) (Finset.single_le_sum (f:=fun i:Axis=> z i^2) (fun i _=>sq_nonneg _) (mem_univ _))
variable {F:ι→Momentum}{x:Bin}(y:Tendsto F l (𝓝 (tmap x)))
include y
private lemma nar : Tendsto (fun i=>narrow (M i) (F i)) l (𝓝 0):=by simpa only [zero_smul,narrow] using (thinning v).smul y
private lemma finger(i:Axis) : Tendsto (fun a=>ds (M a) (F a) i) l (𝓝 (x i:ℂ)):=by
 let z(a):= narrow (M a) (F a) i; let h:= dslope Complex.sin 0
 have he : Tendsto h (𝓝 0) (𝓝 1):=by
    have hy : h 0=1:=by unfold h; rw [dslope_same,(Complex.hasDerivAt_sin _).deriv,Complex.cos_zero]
    rw [←hy]; exact continuousAt_dslope_same.mpr (Complex.hasDerivAt_sin _).differentiableAt -- give .tendsto?
 have hv: Tendsto (fun a=>F a i*h (z a)) l (𝓝 (x i:ℂ)):=by simpa only [comp_def,tmap,z,mul_one] using ((tendsto_pi_nhds.mp y i).mul (he.comp (tendsto_pi_nhds.mp (nar v y) i)))
 refine hv.congr (fun k=>?_); rw [ds_expand,sine, show Complex.sin _= z k*h (z k) from (by simpa only [sub_zero, smul_eq_mul,Complex.sin_zero] using (sub_smul_dslope Complex.sin 0 (z k)).symm)]; unfold z narrow; simp only [Pi.smul_apply,smul_eq_mul]; field_simp [side_ne (M k)]
lemma scale_cost : Tendsto (fun i=>D (M i) (F i)) l (𝓝 (↑(radius x:ℝ)/2:ℂ)):=by
 let t(a):=∑ i:Axis,(ds (M a) (F a) i)^2; let p(a):=narrow (M a) (F a)
 let g:=fun z: Momentum=>rad z - kin z
 have hg : ContinuousAt g 0:=by
    obtain ⟨η,B,h,k,L⟩:=rad_uniform; exact ((L.hol _ (cube_zero η h)).continuousAt).sub (by apply Continuous.continuousAt; unfold kin pl; fun_prop)
 have h0:g 0=2:=by unfold g rad kin pl mag; norm_num [Fir.kin,Fir.pl,Fir.sine]
 have he: Tendsto (fun i=>g (p i)) l (𝓝 2):= h0 ▸ (hg.tendsto.comp (nar v y))
 have hv : Tendsto t l (𝓝 (radius x:ℂ)):=by unfold radius; push_cast; exact tendsto_finsetSum _ (fun i _=>(finger v y i).pow 2)
 apply Tendsto.congr' _ (hv.div he (by norm_num)); filter_upwards [he.eventually (eventually_ne_nhds (Ne.symm (a:= (0:ℂ)) (b:=2) (by norm_num)))] with i w; change t i / g (p i)=_; exact ((eq_div_iff w).mpr (ds_sq _ _).symm).symm
omit y v
open scoped Pointwise
-- unperiodized symbol payoff
abbrev weave (x:Bin) :ℂ:= ∏ i:Axis,skirt (x i)
local notation "P" a:max=> narrow (M a) (F a)
include v y
lemma decking (w:∀ᶠ i in l,Odd (M i).val) : Tendsto (fun a=> (muff 4 (M a) (P a))) l (𝓝 (weave x ^ 4)):=by
 apply Tendsto.pow _ 4; apply tendsto_finsetProd (x:=l) (f:=fun i a=> plank (M a) ((P a) i)) _ ?_; intro i _; have hc:=plank_c v (tendsto_pi_nhds.mp y i) w (x i) rfl; simpa only [narrow,Pi.smul_apply,smul_eq_mul, div_eq_mul_inv,mul_comm _ (_⁻¹)] using hc -- binder names
lemma wrapCost(z: x≠0) (i:Axis) : Tendsto (fun a=> ((γ a:ℂ)⁻¹*bGraph (P a) i)) l (𝓝 (2*(x i:ℂ)/radius x)):=by
 have h: Tendsto (fun k=> ds (M k) (F k) i / D (M k) (F k)) l (𝓝 ((x i:ℂ)/(↑(radius x:ℝ)/2))):= (finger v y i).div (scale_cost v y) (div_ne_zero (by exact_mod_cast (radius_pos x z).ne') (by norm_num))
 convert h using 1; · ext1 k; unfold bGraph ds D; simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv, mul_inv]; field_simp [side_ne (M k)]
 congr 1; field_simp
end YM.CF.Crest.Shore
#print axioms YM.CF.Crest.Shore.scale_cost
#print axioms YM.CF.Crest.Shore.wrapCost
#print axioms YM.CF.Crest.Shore.plank_c
