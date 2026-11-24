import YM.SU5.SatinWard.Resolution.Thermo
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.OS.Semigroup
open Set Metric Filter Asymptotics
open scoped Topology NNReal InnerProductSpace Classical
variable {H:Hilbert}{i:Axis}(S:Semigroup H i)
namespace Gear
local notation "ω"=> S.wax
variable {T: ℝ→ℝ→ H.Op}(K:S.Credits 0 T) {y x t b l r y₀:ℝ}
noncomputable def currentTemp (T:ℝ→ ℝ→ H.Op)(l r t:ℝ):= T (l+t) (r-t) -- analytic on appropriate interval. only need Taylor uniform near. Time orientation.
local notation "Tz"=>currentTemp T l r
lemma wax_sweep (p:0<x)(y:ℝ)(q:0 ≤ y): deriv S.wax (x+y)= deriv S.wax x *ω y:=by
 let A:=fun t:ℝ=>ω t* ω y; have h:HasDerivAt (fun t:ℝ=> S.wax (t+y)) (deriv S.wax (x+y)) x:= by
    let h':= ((S.wax_analytic (show 0<x+y by positivity)).differentiableAt.hasDerivAt).scomp x (by exact (hasDerivAt_id' x).add_const y : HasDerivAt (fun t:ℝ=>t+y) 1 x); rw [one_smul] at h'; exact h'
 have t: HasDerivAt A (deriv S.wax (x+y)) x:= h.congr_of_eventuallyEq (by filter_upwards [lt_mem_nhds p] with t u using S.wax_sq (le_of_lt u) q); exact t.unique (((S.wax_analytic p).differentiableAt.hasDerivAt).mul_const _) -- noncomm? tune
lemma waxD (p:0<b)(hx:2*b ≤ x)(hy:2*b ≤ y) : ‖deriv S.wax x-deriv S.wax y‖ ≤ (2/b)^2 * |x-y|:=by
 let f(t:ℝ):= deriv S.wax t; let Z:= (2/b:ℝ); let Q(t:ℝ):= ω (t-b)
 have he(t:ℝ)(w:b ≤ t) : f t=f b*Q t:=by convert! wax_sweep S p (t-b) (sub_nonneg.mpr w) using 2; ring -- congr
 have a:b ≤ x-b:= by linarith only [p,hx]
 have t:b ≤ y-b:= by linarith only [p,hy]; -- $r_{xy}$
 change ‖f x-f y‖≤ _; rw [he _ (by linarith), he y (by linarith), ←mul_sub]; have hz:0≤Z:= by unfold Z; positivity
 have h: ‖Q x-Q y‖≤Z * |x-y|:=by
    let t':=S.wax_shaking p a t; rw [sub_sub_sub_cancel_right, Real.norm_eq_abs] at t'; exact t'
 refine (norm_mul_le ..).trans ((mul_le_mul (S.wax_slow p) h (norm_nonneg _) hz).trans_eq ?_); unfold Z; ring
variable (p:0<b) (u:4*b≤l)(v:4*b≤r)
local notation "ZK"=> T b b
noncomputable def meshThermo (S:Semigroup H i) (b l r:ℝ) (K:ℝ→ℝ→ H.Op) (t:ℝ) : H.Op:=deriv S.wax (l+t-b)*K b b* S.wax (r-t-b)- S.wax (l+t-b)*K b b* deriv S.wax (r-t-b)
local notation "DZ"=> meshThermo S b l r T
local notation "ϱ" u:max=> (r-u-b)
local notation "Ξ" u:max=> (l+u-b)
include p u v K
lemma heatDerAt (w:|t|≤ b) : HasDerivAt (currentTemp T l r) (meshThermo S b l r T t) t:=by
 have p': b < l+t:=by linarith only [(abs_le.mp w).1,u,p]
 have hz:b < r-t:=by linarith only [(abs_le.mp w).2,v,p] -- second ; same line error
 let f(t):=l+t-b; let g(t):=r-t-b; let F(t:ℝ):= ω (f t); let G(t:ℝ):=ω (g t)
 have he:HasDerivAt (fun t:ℝ=>F t* (ZK)*G t) (DZ t) t:=by
    have H1:HasDerivAt f 1 t:= ((hasDerivAt_id' _).const_add _).sub_const _
    have H2:HasDerivAt g (-1) t:= ((hasDerivAt_id' _).const_sub _).sub_const _
    let ht:= (((S.wax_analytic (show 0<f t from sub_pos.mpr p')).differentiableAt.hasDerivAt).scomp t H1|>.mul_const (ZK)).mul (((S.wax_analytic (show 0<g t from sub_pos.mpr hz)).differentiableAt.hasDerivAt).scomp t H2); simp only [one_smul, neg_one_smul,mul_neg,←sub_eq_add_neg] at ht; exact ht -- `.mul` order from NonCom?
 apply he.congr_of_eventuallyEq; let h := ((show Continuous (fun t:ℝ=>l+t) from (continuous_const.add continuous_id)).tendsto t).eventually (lt_mem_nhds p'); let e:= ((show Continuous (fun t:ℝ=>r-t) from (continuous_const.sub continuous_id)).tendsto t).eventually (lt_mem_nhds hz); filter_upwards [h,e] with u p' q using K p p (le_of_lt p') (le_of_lt q)
local notation "D"=>2/b
lemma currentCena(w:|t|≤ b) : ‖DZ t‖≤ (4/b)*‖ZK‖:=by
 let C:= D; have hC:0≤ C:=by unfold C; positivity
 have ht(a:ℝ)(p':2*b≤a): ‖deriv S.wax a‖≤ D:= (S.wax_slow (by linarith)).trans (div_le_div_of_nonneg_left zero_le_two p (by linarith))
 have h₁:=ht (l+t-b) (by linarith only [u,p,(abs_le.mp w).1]); have h₂:=ht (r-t-b) (by linarith only [v,p,(abs_le.mp w).2]); unfold meshThermo; refine (norm_sub_le ..).trans (le_trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (b:=D *‖ZK‖) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))) (S.wax_pay _) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))) ((norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (S.wax_pay _))) h₂ (norm_nonneg _) (norm_nonneg _)))) (le_of_eq ?_)); ring
omit K p u v in
private lemma productPrice {X:Type*}[NormedRing X](x y z v f:X)(c C d h:ℝ)(u:‖x-z‖ ≤ c)(a:‖y-v‖≤C)(w:‖y‖ ≤ h)(p:‖z‖ ≤ d): ‖x*f*y-z*f*v‖ ≤ (c*h+d*C)*‖f‖:=by
 have hc:0≤c:=(norm_nonneg _).trans u; have hd:0≤d:=(norm_nonneg _).trans p
 rw [show x*f*y-z*f*v=(x-z)*f*y+ z*f*(y-v) from (by rw [_root_.sub_mul,_root_.sub_mul,mul_sub]; abel)]
 refine (norm_add_le ..).trans (le_trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right u (norm_nonneg _))) w (norm_nonneg _) (by positivity : 0≤ c*‖f‖))) ((norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _))) a (norm_nonneg _) (by positivity : 0 ≤ d*‖f‖)))) ?_); exact le_of_eq (by ring)
-- uniforms first-derivative change on named window.
lemma lumD (p₁:|t|≤b)(p₂:|x|≤ b) : ‖deriv (currentTemp T l r) x-deriv (currentTemp T l r) t‖≤ 4 * (2/b)^2 * ‖T b b‖* |x-t|:=by
 let m:= (2/b); let K':=(2/b)^2; let d:= |x-t|; obtain ht:0 < m:=by positivity
 have hp(a:ℝ)(u:a≥ 2*b) : ‖deriv S.wax a‖≤ 2/b:= (S.wax_slow (by linarith)).trans (div_le_div_of_nonneg_left zero_le_two p (by linarith))
 have hL(k:ℝ)(h:|k|≤b) : 2*b ≤ Ξ k ∧ 2*b ≤ ϱ k:=by constructor<;> linarith only [u,v,p,(abs_le.mp h).1,(abs_le.mp h).2]
 let ux:=(hL x p₂).1; let vx:=(hL x p₂).2; let ut:=(hL t p₁).1; let vt:=(hL t p₁).2
 let K0:=T b b; let D₁(a):= deriv S.wax a; have hW (x' y':ℝ)(hx:2*b≤x')(hy:2*b ≤ y')(h:|x'-y'|=d) : ‖D₁ x' - D₁ y'‖ ≤ m^2*d ∧ ‖ω x'-ω y'‖≤ m*d:=by
    rw [←h]; refine ⟨waxD S p hx hy,?_⟩; rw [← Real.norm_eq_abs]; exact S.wax_shaking p (by linarith) (by linarith) -- order
 have hl:=hW (l+x-b) (l+t-b) ux ut (by rw [sub_sub_sub_cancel_right, add_sub_add_left_eq_sub]); have hr:=hW (r-x-b) (r-t-b) vx vt (by rw [sub_sub_sub_cancel_right,sub_sub_sub_cancel_left, abs_sub_comm]) -- `rw` may close. tune.
 rw [(heatDerAt S K p u v p₂).deriv,(heatDerAt S K p u v p₁).deriv]; unfold meshThermo; rw [sub_sub_sub_comm]
 have E:= productPrice _ _ _ _ K0 _ _ _ _ hl.1 hr.2 (S.wax_pay (r-x-b)) (hp (l+t-b) ut); have W:=productPrice _ _ _ _ K0 _ _ _ _ hl.2 hr.1 (hp (r-x-b) vx) (S.wax_pay (l+t-b))
 exact (norm_sub_le ..).trans ((add_le_add E W).trans_eq (by unfold m d K0; ring))
-- Taylor from estimates on a full interval avoiding assumptions about gigantic derivative on only compact-set accum.
lemma price_time(p':|t|≤ b) : ‖currentTemp T l r t-currentTemp T l r 0- t•deriv (currentTemp T l r) 0‖ ≤ 4* (2/b)^2 * ‖T b b‖ * |t| * |t|:=by
 let E:= 4*(2/b)^2; let F(x:ℝ):= currentTemp T l r x-x • deriv (currentTemp T l r) 0; let V:= Set.Icc (-|t|) |t|; have hp(y:ℝ)(u:y∈ V): |y|≤|t|:= abs_le.mpr u
 let Tt(y):= deriv (currentTemp T l r) y- deriv (currentTemp T l r) 0; have hc(y:ℝ)(vp:y∈V): HasDerivAt F (Tt y) y:=by
    let h:= heatDerAt S K p u v ((hp y vp).trans p'); unfold F Tt; convert! h.sub ((hasDerivAt_id' _).smul_const (deriv (currentTemp T l r) 0)) using 1; rw [h.deriv,one_smul]
 have hz:0≤|t|:=abs_nonneg _; have hq(y:ℝ)(vp:y∈V): ‖deriv F y‖≤ E*‖T b b‖* |t|:= by
    rw [(hc y vp).deriv]; refine (lumD (t:=0) S K p u v (by simp; linarith) ((hp y vp).trans p')).trans ?_; rw [sub_zero]; exact mul_le_mul_of_nonneg_left (hp y vp) (by positivity) -- unfolds E
 have W:= Convex.norm_image_sub_le_of_norm_deriv_le (s:=V) (𝕜:=ℝ) (f:=F) (fun i h=>(hc i h).differentiableAt) hq (convex_Icc ..) (x:=0) (show (0:ℝ)∈ V from ⟨neg_nonpos.mpr hz,hz⟩) (y:=t) (show t∈V from abs_le.mp (le_refl _)); rw [sub_zero,Real.norm_eq_abs] at W; refine Eq.trans_le (congrArg norm (?_: _= F t-F 0)) W; unfold F; rw [zero_smul,sub_zero]; abel
#print axioms price_time
#print axioms heatDerAt
end Gear
end YM.OS.Semigroup
