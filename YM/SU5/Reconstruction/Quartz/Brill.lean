import YM.SU5.Reconstruction.Quartz.Skype
import YM.SU5.Reconstruction.Quartz.Felicity
import YM.SU5.Reconstruction.Vermont.Mintage
/-! # second frame coordinates & bridge analysis -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval
open CrossedFrame Clasp Picket Lens Ravin BridgeClub Anvil
variable (a b:Axis)
noncomputable def path (v:Du):E4:=((v.1+v.2)/2) • basis a+((v.1-v.2)/2) • basis b
@[fun_prop] lemma path_cont: Continuous (path a b):= by unfold path;fun_prop
lemma path0:path a b 0=0:= by simp[path]
lemma shift_clock(t u:ℝ) : path a b (u+t,t)= t • basis a + path a b (u,0):= by simp[path]; ext i; by_cases h:i=a<;>  by_cases q:b=a<;> by_cases w:i=b<;> simp [h,w,q]<;> ring -- tune
variable {a b} (p:b ≠ a)
local notation "c"=> path a b
include p
lemma homeward (u:Du)(s:ℝ) : path a b (Waltz.swap s u)=Picket.move a b (-s) (c u):=by
 rw [at_swap]; ext i; rcases eq_or_ne i a with h| h; · rw [h,eye_high p]; simp[path,p,p.symm,Real.sinh_eq,Real.cosh_eq]; ring
 rcases eq_or_ne i b with u|q; · rw [u,eye_low p]; simp[path,p,p.symm,Real.sinh_eq, Real.cosh_eq]; ring
 rw [others _ _ _ h q]; simp [path,h,q]
omit p
noncomputable def crossprice(d:ℝ)(z:ℂ):Ba:= ((d:ℂ)*Complex.exp (-z), -(d:ℂ)*Complex.exp z)
noncomputable def turning_shift(d s:ℝ):Du:=(d*Real.exp (-s), -d*Real.exp s)
@[fun_prop] lemma crossprice_analytic(d:ℝ): Differentiable ℂ (crossprice d):=by unfold crossprice; fun_prop
lemma price_rail(d s:ℝ): crossprice d s= Largo (turning_shift d s):= by unfold crossprice Largo turning_shift; push_cast; rfl
lemma lunar(d s:ℝ): crossprice d ((s:ℂ)+ κ*Complex.I)=petal s d:=by
 have hx: Complex.exp ((κ:ℂ)*Complex.I)=Complex.I:= by unfold κ Quarterπ; push_cast; exact Complex.exp_pi_div_two_mul_I -- order tune
 have hy: Complex.exp (-((κ:ℂ)*Complex.I))= -Complex.I:= by rw [Complex.exp_neg,hx]; simp
 unfold crossprice petal; ext1; · rw [neg_add, Complex.exp_add, hy]; dsimp; push_cast; ring
 rw[Complex.exp_add,hx]; push_cast; ring_nf
-- max on compact
lemma Power (d:ℝ): ∃ M:ℝ,∀ u∈ D, pressure (Forge (crossprice d u))+pressure (Eddy (crossprice d u)) ≤M:= by
 let f(u:ℂ):=pressure (Forge (crossprice d u))+pressure (Eddy (crossprice d u))
 let h: IsCompact D:= IsCompact.reProdIm isCompact_Icc isCompact_Icc
 have t: Continuous f:=by unfold f pressure Forge Eddy crossprice; fun_prop
 obtain ⟨v,p⟩:=(h.image t).bddAbove; exact ⟨v,fun u a=> p (Set.mem_image_of_mem f a)⟩
noncomputable def ceilingCost(d:ℝ):= 1+d^2*(Real.exp 3)^2*4
lemma ceiling_ok (d:ℝ): 1≤ceilingCost d:= le_add_of_nonneg_right (by positivity)
lemma wind (z:ℂ)(d:ℝ)(p:z∈D): pressure (Eddy (crossprice d z)) ≤ ceilingCost d*z.im:=by
 let y:=z.im; obtain ⟨h,q⟩:=passion _ (abs_le.mpr p.1); let t:= Real.exp 3; have v:Real.sin y^2≤y^2:= Real.sin_sq_le_sq; have he:0≤y:=p.2.1; have hy:y^2≤2*y:=by nlinarith [show y≤2 from p.2.2.trans paid] -- syntax
 have hq (a:ℝ)(p:0≤a)(e:a≤ Real.exp 3) : (d*(a*Real.sin y))^2 ≤ d^2*t^2*(2*y):= by simp_rw [mul_pow]; rw[← mul_assoc]; gcongr ; exact v.trans hy
 unfold pressure Eddy crossprice; simp only [Complex.mul_im,Complex.neg_im,Complex.neg_re, Complex.ofReal_re,Complex.ofReal_im,Complex.exp_im, zero_mul, add_zero,Real.sin_neg, mul_neg,neg_sq,neg_mul] -- tune
 unfold ceilingCost; nlinarith [hq _ (Real.exp_pos z.re).le h,hq _ (Real.exp_pos (-z.re)).le q]
variable {H K E:Hilbert} {Z:Type*}[TopologicalSpace Z](C:Clasp K H E)(S:OS.Semigroup H a)(B:H.Op)
noncomputable def rateTime (u:Du):H.Op:=parcelUp S (path a b u) B
local notation "A"=> rateTime (b:=b) S B
-- v Rank.Integer
lemma strollWalk (U:Z→H.Op)(p:∀ z,Pays (U z))(T:∀ x:H, Continuous (fun i=>U i x))(f:Z→ H)(h:Continuous f):Continuous (fun i=> U i (f i)):= by
 apply continuous_iff_continuousAt.mpr; intro x; apply Metric.tendsto_nhds.mpr; intro ε v
 filter_upwards [h.continuousAt.tendsto.eventually (Metric.ball_mem_nhds (f x) (half_pos v)), (T (f x)).continuousAt.tendsto.eventually (Metric.ball_mem_nhds (U x (f x)) (half_pos v))] with y k e
 apply (dist_triangle _ (U y (f x)) _).trans_lt; have hv: dist (U y (f y)) (U y (f x))= dist (f y) (f x):= by rw[dist_eq_norm,dist_eq_norm,←map_sub,@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,(p y).ordinary]
 rw [hv]; linarith [mem_ball.mp k,mem_ball.mp e]
lemma rateAccess{b:Axis}(g:Z→H)(h:Continuous g)(x:Z→Du)(p:Continuous x) : Continuous (fun i=> rateTime (b:=b) S B (x i) (g i)):=by
 let v(i:Z):=path a b (x i); have hu: Continuous v:= (path_cont ..).comp p
 unfold rateTime parcelUp; simp_rw [mul_apply_eq_comp]; apply strollWalk _ (fun _=> mobile ..) (fun X=>(S.unit.moves X).comp hu); refine B.continuous.comp (strollWalk _ (fun _=>mobile ..) (fun X=>(S.unit.moves X).comp hu.neg) g h)
lemma boostStar(s:ℝ): star (boost C s)=boost C (-s):= by unfold boost; rw [(left_credentials ..).2.1,neg_div,neg_neg]; simp -- tune
lemma ascentWalk (u:Z→ℝ)(p:Continuous u)(x:Z→H)(h:Continuous x) : Continuous fun i=> ascend (u i) C B (x i):=by
 unfold ascend; simp_rw [boostStar,mul_apply_eq_comp]; apply strollWalk _ (fun _=> boost_pays ..) (fun X=> (Picket.warm C X).comp p); apply B.continuous.comp (strollWalk _ (fun _=> boost_pays ..) (fun X=>(Picket.warm C X).comp p.neg) x h)
end YM.Quartz.Waltz
