import YM.SU5.Reconstruction.Seams.Hole
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
/-!
# End-segment: establish existence of real clock preserving the signal in any paid scripted connection.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens.River
open Function Set Filter Spectral Analysis Metric OS.Semigroup ConePrice Sail MeasureTheory Complex CF.Floral
open scoped BigOperators Topology Interval InnerProductSpace
variable {a b c:ℝ}{f:ℂ→ℂ}
local notation "H"=> inside
local notation "P"=> {z:ℂ|0≤ z.re}
local notation "Ω" => Ι 0 a
local notation "j" u:max => (↑(u:ℝ):ℂ)
def flux (f:ℂ→ℂ) (a:ℝ)(z:ℂ):= ∫ t in (0:ℝ)..a, f (z + (t:ℂ)*I)
variable (h:0<a) (v:∀ x:ℂ,0≤ x.re→‖f x‖≤c) (D:DifferentiableOn ℂ f inside) (F: Continuous f)
include v h
lemma balance (z:ℂ)(w:0<z.re) : ‖flux f a z‖ ≤ c*a:= by
 unfold flux; apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const _); exact congrArg (c*·) (abs_of_pos (sub_pos.mpr h) |>.trans (sub_zero a)) |>.le
 intro z p; apply v; simpa using w.le
omit h
omit v in
private lemma seat (c0:ℝ)(p:ℂ) (k:c0<p.re) : closedBall p c0⊆ inside:=by
 intro z e; rw [mem_closedBall,dist_eq_norm] at e; change 0< z.re; have t:= (abs_le.mp ((abs_re_le_norm (z-p)).trans e)).1; rw [sub_re] at t; linarith
include D in
lemma pipe (z:ℂ)(r:ℝ)(p:0<r)(w:r<z.re): ‖deriv f z‖ ≤ c/r:= c_deriv D p (seat _ _ w) (fun z e=>v z (show 0< z.re from e).le) -- include v? seat using v unint. tune
include F D
lemma polish (a:ℝ): Hol inside (flux f a):=by
 intro z p; let U(t:ℝ):= j t*I; let g (z:ℂ)(t:ℝ):= z+U t; have hg (z:ℂ): Continuous (g z):= by unfold g U; fun_prop -- no
 have pot(w:ℂ)(t:ℝ) : (g w t).re=w.re:= by simp [g,U]
 let G(z:ℂ):= f∘ g z; let G'(z:ℂ):= deriv f∘ g z; have dg:Continuous (G' z):= (D.deriv open_inside).continuousOn.comp_continuous (hg z) (fun t=>(by change 0<(g z t).re; rwa [pot])) -- p R?)
 let r:= z.re/2; let T:= {x:ℂ| r<x.re}; have b:0<r:= half_pos (show 0< _ from p)
 have e:z∈T:= half_lt_self (show 0< z.re from p)
 refine ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=G) (F':=G') (a:=0) (b:=a) (μ:=volume) ((isOpen_lt continuous_const continuous_re).mem_nhds e) (Eventually.of_forall fun _=> (F.comp (hg _)).aestronglyMeasurable) ((F.comp (hg z)).intervalIntegrable _ _) dg.aestronglyMeasurable (bound:=fun _=>c/r) (ae_of_all volume (fun t _ x hU=> pipe v D _ r b (pot x t |>.symm ▸ hU))) intervalIntegrable_const ?_).2).differentiableAt.differentiableWithinAt
 apply ae_of_all; intro t h x eT;  change HasDerivAt (f ∘ fun y=> y+ U t) (deriv f (g x t)) x; simpa only [mul_one,one_mul] using ((D.differentiableAt (open_inside.mem_nhds (show g x t∈ H from (show 0<(g x t).re from pot x t |>.symm ▸ (b.trans (show r < x.re from eT)))))).hasDerivAt).comp x ((hasDerivAt_id' x).add_const (U t)) -- needs mul-one
omit v D F
lemma edify (f:ℂ→ℂ)(a y x:ℝ): flux f a (x+y*I) = ∫ t:ℝ in y..(a+y), f (x + (t:ℂ)*I) :=by
 let g (t:ℝ):=f (x+(t:ℂ)*I); have h:= intervalIntegral.integral_comp_add_right (a:=0) (b:=a) g y; rw [zero_add] at h; rw [flux,show (fun t:ℝ=> f ((x:ℂ)+ y*I+t*I))=(fun t:ℝ=>g (t+y)) from ?_]; exact h
 ext1 t; unfold g; apply congrArg; push_cast; ring
include F D v h
lemma beaches (z:ℂ) (u:0<z.re): ‖flux f a z - flux f a (z.im * I)‖ ≤ c*z.re+c*z.re:=by
 let x:= z.re; let y:= z.im; let A:=a+y;
 let W:ℂ:= ⟨x,A⟩; let L:ℂ:=⟨0,y⟩
 let h1(x':ℝ):= ∫ t:ℝ in y..A, f (x'+ t*I)
 let h2(y':ℝ):= ∫ t:ℝ in 0..x,f ((t:ℂ)+ y'*I)
 have c1 : h1 x=flux f a z:=by unfold h1; rw [← edify,show (↑x:ℂ)+↑y*I=z from re_add_im z] -- tune
 have c2 : h1 0=flux f a (z.im * I):=by unfold h1; rw [← edify, Complex.ofReal_zero,zero_add]
 have ht : h2 y-h2 A + I • h1 x - I • h1 0=0:= by
   apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f L W F.continuousOn; apply D.mono; intro p w; change 0 < p.re; exact lt_of_le_of_lt (le_min (show 0≤L.re from le_refl _) u.le) (w.1.1)
 have he (p:ℝ) : ‖h2 p‖≤ c*x:= by
   refine (intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t:ℝ=>_) (C:=c) ?_).trans_eq (congrArg (c*·) ((abs_of_pos (sub_pos.mpr u)).trans (sub_zero _)))
   intro t b; exact v _ (by simpa using ((mem_Ioc.mp ((uIoc_of_le (show 0≤x from u.le)) ▸ b)).1.le)) -- lemma args
 rw [← c1, ← c2]
 have hk: I • (h1 x - h1 0)=h2 A-h2 y:= by rw [smul_sub]; grind -- linear abel
 exact (Eq.symm (show ‖I • (h1 x - h1 0)‖=_ by simp [norm_smul])).trans_le (hk.symm ▸ le_trans (norm_sub_le ..) (add_le_add (he A) (he y)))
omit F h
lemma costs_vertical (x:ℝ): ‖f (1 + (x:ℂ)*I)- f 1‖ ≤ c / (1/3) * |x|:= by
 let K: Set ℂ:= {x| 1/2 < x.re}; let z:ℂ:= 1+(x:ℂ)*I; have hK: Convex ℝ K:= convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear _; have hz:K⊆ H:= fun x u=> lt_trans (by norm_num: (0:ℝ)<1/2) (show 1/2<x.re from u); refine (hK.norm_image_sub_le_of_norm_deriv_le (fun x b=> D.differentiableAt (open_inside.mem_nhds (hz b))) (fun x b=> pipe v D x _ (by norm_num) (lt_trans (by norm_num : (1:ℝ)/3<1/2) b)) (show (1:ℂ)∈K from (by unfold K; norm_num)) (show z∈K from (by unfold z K; norm_num))).trans_eq (by simp [norm_mul,Real.norm_eq_abs,z])
end YM.Lens.River
