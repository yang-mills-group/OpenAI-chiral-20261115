import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.PSeries
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.SatinExist.Lancet
open Function Filter Metric Set Complex
open scoped Topology BigOperators
local notation "D"=> {z:ℂ|0<z.re}
variable (a x:ℝ)
def gate (a:ℝ)(z:ℂ):ℂ:= (z-a)/(z+a)
def returning (a:ℝ)(z:ℂ):ℂ:= (a:ℂ)*(1+z)/(1-z)
variable (p:0<a)
include p
lemma paid {z:ℂ}(h:z∈ D) : z+(a:ℂ) ≠ 0:=by
 intro t; have e:=congrArg Complex.re t; simp only [Complex.add_re, Complex.ofReal_re,Complex.zero_re] at e; linarith only [show 0< z.re from h,p,e]
lemma passes {z:ℂ}(h:z∈D):‖gate a z‖<1:=by
 unfold gate; rw [norm_div]; apply (div_lt_one (norm_pos_iff.mpr (paid a p h))).mpr
 apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp; rw [Complex.sq_norm,Complex.sq_norm]; simp only [Complex.normSq_apply, sub_re,sub_im,add_re,add_im, Complex.ofReal_re, Complex.ofReal_im]; nlinarith only [mul_pos (show 0<z.re from h) p]
private lemma close_to {z:ℂ}(h:z∈D): returning a (gate a z)= z:=by
 let u:= gate a z; have he:1-u≠0:= sub_ne_zero.mpr (fun y=> by have e:=passes a p h; change ‖u‖<1 at e; simp [← y] at e); change a*(1+u)/(1-u)=z; rw [div_eq_iff he]; unfold u gate; have hx:=paid a p h; field_simp; ring
omit p
private lemma shares {z:ℂ}(p:z∈ Metric.ball (0:ℂ) 1): 1-z≠0:= by intro h; rw [←sub_eq_zero.mp h] at p; simp at p
include p
private lemma controls {z:ℂ}(h:z∈ Metric.ball (0:ℂ) 1): returning a z ∈ D:=by
 have he:= shares h; change 0< (a*(1+z)/(1-z):ℂ).re
 have hp: 0< Complex.normSq (1-z):= Complex.normSq_pos.mpr he
 have hx:‖z‖^2<1:= (pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp h) (by norm_num))
 rw [Complex.sq_norm,Complex.normSq_apply] at hx
 simp only [Complex.div_re,Complex.add_re, Complex.sub_re, Complex.mul_re,Complex.one_re,Complex.ofReal_re,Complex.add_im, Complex.sub_im, Complex.mul_im,Complex.one_im,Complex.ofReal_im,zero_mul,sub_zero,zero_add, add_zero,zero_sub]; rw [←add_div, lt_div_iff₀ hp]; nlinarith only [mul_pos p (sub_pos.mpr hx)]
-- realizes the B factor estimates from contraction's Schwarzer, in this whole chamber
variable (K:ℝ)
structure Aim (f:ℂ→ℂ) (K:ℝ) : Prop where
 holo: DifferentiableOn ℂ f D
 price(z:ℂ)(p:0<z.re): ‖f z‖ ≤ K
variable {f:ℂ→ℂ}
lemma one_zero(h:Aim f K)(z:f a=0): ∃ g:ℂ→ℂ, Aim g K ∧∀ x∈D,f x=g x*gate a x:=by
 let g (i:ℂ):= dslope f a i*(i+a)
 have ht : DifferentiableOn ℂ g D:= ((Complex.differentiableOn_dslope (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds (show (a:ℂ)∈D from p))).2 h.holo).mul (differentiableOn_id.add (differentiableOn_const _))
 have he(i:ℂ)(y:i∈ D):f i=g i*gate a i:=by
    by_cases h:i=(a:ℂ)
    · rw [h,z]; simp [gate]
    unfold gate g; rw [dslope_of_ne f h]; simp [slope_def_module,z]; have hy:=paid a p y; field_simp
 let F:= f ∘ returning a; let u:= Metric.ball (0:ℂ) 1; have hb : F 0=0:= by unfold F returning; simpa using z
 have hF:DifferentiableOn ℂ F u:= h.holo.comp (DifferentiableOn.div ((differentiableOn_const _).mul ((differentiableOn_const _).add differentiableOn_id)) ((differentiableOn_const _).sub differentiableOn_id) fun _ p => shares p) (fun i y=> controls a p y)
 have hv:MapsTo F u (Metric.closedBall (F 0) K) := by rw [hb]; intro i hx; exact mem_closedBall_zero_iff.mpr (h.price _ (controls a p hx))
 refine ⟨g,⟨ht,fun i t=>?_⟩,he⟩; let y: i∈D:= t
 have hz : ContinuousAt g i := ht.continuousOn.continuousAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds y)
 apply le_of_tendsto_of_frequently (hz.tendsto.norm.mono_left (nhdsWithin_le_nhds (s:= ({(a:ℂ)}ᶜ))))
 haveI : (𝓝[({(a:ℂ)}ᶜ)] i).NeBot := by
    rcases eq_or_ne i (a:ℂ) with e|e; · rw [e]; exact inferInstance
    rw [nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds e)]; exact inferInstance
 refine Eventually.frequently ?_; filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds y)] with w q y
 have hp:= Complex.dist_le_div_mul_dist_of_mapsTo_ball hF hv (mem_ball_zero_iff.mpr (passes a p y))
 have hg:0<‖gate a w‖:=norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr q) (paid a p y))
 rw [show F (gate a w)=f w from congrArg f (close_to a p y), hb,he w y, dist_zero_right, dist_zero_right,norm_mul,div_one] at hp; exact le_of_mul_le_mul_right hp hg
omit p
private lemma price_ring (f:ℂ→ℂ)(h:Aim f K)(x:ℝ)(b:0<x)(Z:ℕ→ℝ)(s:StrictMono Z) (n:ℕ)(e:∀ i∈Finset.range n,x<Z i)(p:∀ i∈Finset.range n, f (Z i)=0): ‖f (x:ℂ)‖ ≤ K* (∏ i∈Finset.range n,(Z i-x)/(Z i+x)):=by
 induction n generalizing f with
 | zero=> simp [h.price x b]
 | succ n ih=>
    let a:= Z n; have ha := (e n (Finset.mem_range.mpr (Nat.lt_succ_self _)))
    obtain ⟨g,t,G⟩:= one_zero a (b.trans ha) K h (p _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))
    have ht(i)(v:i∈Finset.range n):i∈ Finset.range (n+1):= Finset.mem_range.mpr ((Finset.mem_range.mp v).trans (Nat.lt_succ_self _))
    have H(i)(v:i∈ Finset.range n): g (Z i)=0:=by
       have e':= e i (ht i v); have hh : (Z i:ℂ)∈D:= b.trans e'; have hx:gate a (Z i)≠0:= div_ne_zero (sub_ne_zero.mpr (fun e=> (s (Finset.mem_range.mp v)).ne (Complex.ofReal_injective e))) (paid a (b.trans ha) hh)
       exact (mul_eq_zero.mp ((G _ hh).symm.trans (p i (ht i v)))).resolve_right hx
    have hg : ‖gate a x‖ = (Z n-x)/(Z n+x):=by rw [gate,norm_div,← Complex.ofReal_sub,←Complex.ofReal_add, Complex.norm_real,Complex.norm_real, Real.norm_eq_abs,Real.norm_eq_abs, abs_of_neg (sub_neg.mpr ha),abs_of_pos (add_pos b (b.trans ha)),neg_sub, add_comm a x] -- direction
    rw [Finset.prod_range_succ,←mul_assoc, ←hg,G (x:ℂ) b,norm_mul]; exact mul_le_mul_of_nonneg_right (ih g t (fun i v=> e _ (ht i v)) H) (norm_nonneg _)
-- can't shut every large pixel `n+1` in ray's own fixed chamber
lemma cont_rail (f:ℂ→ℂ)(K:ℝ)(k:0≤K)(h:Aim f K)(d x:ℝ)(g:0<d)(r:0<x)(v:f x≠0): ∃ᶠ i:ℕ in atTop, f (↑(i:ℕ)*d:ℂ)≠0:=by
 by_contra p; push Not at p; obtain ⟨A,p⟩:= eventually_atTop.mp p
 obtain ⟨n,k1,v',hx⟩:= ((eventually_ge_atTop A).and ((eventually_gt_atTop (0:ℕ)).and ((tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const g |>.eventually (eventually_gt_atTop x)))).exists -- tune
 let Z(i:ℕ):ℝ:=(i+n:ℕ)*d; have hs:StrictMono Z:= fun i j h=> mul_lt_mul_of_pos_right (by exact_mod_cast Nat.add_lt_add_right h n) g
 have he(i): x<Z i:=show _ from lt_of_lt_of_le (by simpa [Z] using (show x<(n:ℝ)*d from hx):x<Z 0) (hs.monotone (Nat.zero_le i))
 have hL(i): f (Z i:ℂ)=0:=by unfold Z; norm_cast; push_cast; simpa using p _ (show A≤ i+n from k1.trans (Nat.le_add_left ..))
 let c:= 2*x/( (Z 0+x)+d)
 have hc: 0<c:= div_pos (by linarith) (by linarith [he 0])
 let V(i:ℕ):= (Z i-x)/(Z i+x)
 have hv(i:ℕ): V i ≤ Real.exp (-c*(1/((i:ℝ)+1))) := by
    apply le_trans _ (Real.add_one_le_exp _); unfold V
    have h':0< Z 0+x+d:=by linarith [he 0]
    have ht:0<(i:ℝ)+1:=by positivity
    have e:0<Z i+x:=by linarith [he i]
    rw [show (Z i-x)/(Z i+x)=1- 2*x/(Z i+x) by field_simp; ring,show -c*(1/((i:ℝ)+1))+1=1-2*x/(((i:ℝ)+1)*(Z 0+x+d)) from (by unfold c; field_simp; ring)]
    gcongr; rw [show Z i+x=(i:ℝ)*d+(Z 0+x) by unfold Z; push_cast; ring]; nlinarith [show 0≤(i:ℝ) by positivity, mul_nonneg (show 0≤(i:ℝ) by positivity) (show 0≤ Z 0 + x by linarith [he 0])]
 let a(i:ℕ):=1/((i:ℝ)+1)
 have ht:Tendsto (fun i:ℕ=> ∑ j∈Finset.range i, -c*a j) atTop atBot:=by simp_rw [←Finset.mul_sum]; exact Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)
 have hy:= v; have he' := le_of_tendsto_of_tendsto (tendsto_const_nhds (x:= ‖f (x:ℂ)‖)) (((Real.tendsto_exp_atBot.comp ht).const_mul K)) (Eventually.of_forall fun i:ℕ=>?_)
 swap
 · apply (price_ring K f h _ r Z hs i (fun _ _=>he _) (fun _ _=>hL _)).trans
   apply mul_le_mul_of_nonneg_left _ k; rw [Function.comp_apply,Real.exp_sum]; exact Finset.prod_le_prod (fun i _=> div_nonneg (sub_pos.mpr (he i)).le (by linarith [he i])) (fun i _=>hv i)
 rw [mul_zero] at he'; exact not_le_of_gt (norm_pos_iff.mpr v) he'
end YM.SatinExist.Lancet
