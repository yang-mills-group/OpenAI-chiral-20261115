import YM.CF.Mew.Tube
import YM.CF.BProof.Floral.Lace
import YM.CF.BProof.Floral.Difference
set_option autoImplicit false
noncomputable section
open Function NormedSpace Filter Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal Classical ComplexConjugate
namespace YM.CF.Floral
variable {f:ℂ→ℂ}{r L:ℝ}
open Set Mew
local notation "Z(" t ")"=> circleMap (0:ℂ) r t
lemma C_circle (h:Hol (closedBall 0 r) f)(_g:0<r)(u:ℂ)(p:u∈disk r): (∫ t:ℝ,(circleMap 0 r t)*(circleMap 0 r t-u)⁻¹*f (circleMap 0 r t) ∂sky)= f u:=by
 let X(t):= Z(t)*(Z(t)-u)⁻¹*f Z(t); let A:=∫ t in Ioc 0 roll, X t; have ht:= h.circleIntegral_sub_inv_smul p; have he(t:ℝ): deriv (circleMap (0:ℂ) r) t • ((Z(t)-u)⁻¹ • f Z(t))= Complex.I • X t:=by rw [deriv_circleMap]; unfold X; simp_rw [smul_eq_mul]; ring
 change (∫ t in (0:ℝ)..roll,deriv (circleMap (0:ℂ) r) t • ((Z(t)-u)⁻¹ • f Z(t)))=(2*Real.pi*Complex.I) • f u at ht; simp_rw [he] at ht; rw [intervalIntegral.integral_smul, intervalIntegral.integral_of_le roll_pos.le,show 2*(Real.pi:ℂ)*Complex.I= Complex.I*(roll:ℝ) from (by unfold roll; push_cast; ring),mul_smul] at ht
 have hk:A= roll • f u:= smul_right_injective ℂ Complex.I_ne_zero ht; unfold sky; rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.mpr roll_pos).le]; change roll⁻¹ • A=f u; rw [hk,inv_smul_smul₀ roll_pos.ne']
lemma znorm (t:ℝ)(p:0 ≤ r): ‖Z(t)‖=r:=by rw [norm_circleMap_zero,abs_of_nonneg p]
private lemma C_zero (h:Hol (closedBall 0 r) f)(g:0<r): (∫ t:ℝ,f Z(t)∂sky)=f 0:=by
 have he(t:ℝ):Z(t) ≠0:=norm_pos_iff.mp ((znorm t g.le).symm ▸ g)
 simpa only [sub_zero, mul_inv_cancel₀ (he _),one_mul] using C_circle h g 0 (mem_ball_self g)
def stew(r:ℝ)(t:ℝ):ℂ:=(circleMap 0 r t-1)⁻¹
variable (g:1<r)
include g
private lemma stud (t:ℝ): Z(t)-1≠0:=by intro h; have hp:=znorm t (zero_lt_one.trans g).le; rw [sub_eq_zero.mp h,norm_one] at hp; exact g.ne hp
private lemma shape_k : Continuous (stew r):= ((continuous_circleMap ..).sub continuous_const).inv₀ (fun t=> stud g t) -- colon
lemma chords (h:Hol (closedBall 0 r) f): (∫ t:ℝ,stew r t*(f Z(t)-conj (f Z(t)))∂sky)= f 1-f 0:=by
 let c(t):=stew r t; let V(t):=f Z(t); have ht:Continuous V:= h.continuousOn.comp_continuous (continuous_circleMap ..) (fun t=> sphere_subset_closedBall (circleMap_mem_sphere 0 (zero_lt_one.trans g).le t)); let k(t:ℝ):=c t*V t; let q(t):=c t*conj (V t)
 have hk(t:ℝ):Z(t)*c t=c t+1:=by unfold c stew; field_simp [stud g t]; ring -- tune
 have hm: (∫ i,k i ∂sky)= f 1-f 0:=by
    apply eq_sub_of_add_eq; rw [←C_zero h (zero_lt_one.trans g)]; change (∫ i,k i ∂sky)+(∫ i,V i∂sky)=_; rw [←integral_add (show Integrable k sky from tourB _ ((shape_k g).mul ht)) (tourB _ ht)]
    have hh:= C_circle h (zero_lt_one.trans g) 1 (d1 g); change (∫ t,Z(t)*c t*V t ∂sky)=_ at hh; simp_rw [hk,add_mul, one_mul] at hh; exact hh
 have hg(t:ℝ): r < r*r:=by nlinarith
 let R:ℂ:=(r*r:ℝ); let K(z:ℂ):=z*(R-z)⁻¹*f z
 have hy(z){e:z∈closedBall 0 r}: R-z≠0:=by
    intro h; have he:=mem_closedBall_zero_iff.mp e; rw [←sub_eq_zero.mp h, show R= ((r*r:ℝ):ℂ) from rfl,norm_real,Real.norm_of_nonneg (by nlinarith)] at he; nlinarith [hg 0]
 have hH:Hol (closedBall 0 r) K:=by intro z e; apply DifferentiableWithinAt.mul _ (h z e); exact differentiableWithinAt_id.mul (((differentiableWithinAt_const ..).sub differentiableWithinAt_id).inv (hy _ (e:=e)))
 have hp(t): conj (q t)=K Z(t):=by
    unfold q V c stew K; apply Eq.trans (map_mul conj _ _); rw [starRingEnd_self_apply,map_inv₀,map_sub,map_one]; congr 1
    have hz:Z(t) ≠0:=norm_pos_iff.mp ((znorm t (zero_lt_one.trans g).le).symm ▸ zero_lt_one.trans g); have hx:R-Z(t)≠0:=hy _ (e:=by rw [mem_closedBall_zero_iff,znorm t (zero_lt_one.trans g).le]); have hh:conj Z(t)-1≠0:=by rw [←map_one conj,←map_sub]; exact (star_eq_zero.not).mpr (stud g t) -- tune
    have hg:conj Z(t)*Z(t)=R:=by rw [conj_mul',znorm t (zero_lt_one.trans g).le]; simp [R,pow_two]; -- maybe simp uses coe_mul
    field_simp; linear_combination -hg -- sign tune
 have hr: (∫ i,q i∂sky)=0:=by
    apply star_injective; rw [star_zero]; change conj _=0; rw [← integral_conj]; simp_rw [hp,C_zero hH (zero_lt_one.trans g)]; simp [K]
 simp_rw [mul_sub]; change (∫ t,k t-q t∂sky)= _; rw [integral_sub (tourB k ((shape_k g).mul ht)) (tourB q ((shape_k g).mul ht.star)),hr, hm,sub_zero]
lemma smoke(k:ℂ)(t:ℝ) : ‖stew r t*(k-conj k)‖ ≤ 2/(r-1)* |k.im|:=by
 have he:k-conj k=(2*k.im:ℝ)*Complex.I:=by apply Complex.ext <;> simp; ring
 have hp:=norm_sub_norm_le Z(t) 1; rw [znorm t (zero_lt_one.trans g).le,norm_one] at hp
 unfold stew; simp_rw [norm_mul,he, norm_mul, norm_I,mul_one,norm_real,norm_inv,Real.norm_eq_abs,abs_mul,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)]
 refine (mul_le_mul_of_nonneg_right (inv_anti₀ (sub_pos.mpr g) hp) (by positivity)).trans_eq ?_; rw [div_eq_mul_inv]; ring
omit g
lemma imaginary_t {I:Type*}(S:Finset I)(w:I→ℝ)(F:I→ℂ→ℂ)(k:1<L)(p:∀ i∈ S,0≤ w i)(t:∀ i∈S,Hol (disk L) (F i)){a:ℝ}(H:∀ z∈disk L,(∑ i∈S,w i * |(F i z).im|) ≤ a): (∑ i∈S,w i* ‖F i 1-F i 0‖) ≤ 2/(L-1)*a:=by
 refine ge_of_tendsto ((tendsto_const_nhds.div (show Tendsto (fun i:ℝ=>i-1) (𝓝[<] L) (𝓝 (L-1)) from ContinuousWithinAt.tendsto (f:=fun i:ℝ=>i-1) (by fun_prop)) (sub_pos.mpr k).ne').mul tendsto_const_nhds) ?_
 filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds k)] with r hr g
 change (1:ℝ)<r at g; change r<L at hr; let Q(i:I)(y:ℝ):= stew r y*(F i (circleMap 0 r y)-conj (F i (circleMap 0 r y)))
 have ht(y:ℝ):circleMap 0 r y∈disk L:=mem_ball_zero_iff.mpr ((znorm y (zero_lt_one.trans g).le).trans_lt hr)
 have hu(i)(v:i∈S): Integrable (Q i) sky:=by have hx:Continuous (fun y:ℝ=>F i (circleMap 0 r y)):= (t i v).continuousOn.comp_continuous (continuous_circleMap ..) ht; exact tourB _ ((shape_k g).mul (hx.sub hx.star))
 let K(i:I)(y):=w i*‖Q i y‖; have hK(i)(v:i∈S): Integrable (K i) sky:= ((hu i v).norm).const_mul _; let X:=2/(r-1)
 change _ ≤ X*a; have he: ∀ y:ℝ,(∑ i∈S,K i y) ≤ X*a:=fun y=> (Finset.sum_le_sum (g:=fun i=> X*(w i*|(F i (circleMap 0 r y)).im|)) (fun i v=> (mul_le_mul_of_nonneg_left (smoke g ..) (p i v)).trans_eq (mul_left_comm ..))).trans (by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (H _ (ht y)) (by unfold X; have h:=sub_pos.mpr g; positivity))
 have hH:=integral_mono (integrable_finsetSum _ hK) (integrable_const (μ:=sky) (X*a)) he
 rw [integral_finsetSum _ hK,integral_const, probReal_univ,one_smul] at hH; apply le_trans _ hH
 refine Finset.sum_le_sum fun i v=>?_ ; have hg:= chords g ((t i v).mono (closedBall_subset_ball hr)); unfold K; rw [integral_const_mul,←hg]; exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (p i v)
end YM.CF.Floral
