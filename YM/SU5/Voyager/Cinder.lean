import Mathlib.Analysis.Complex.Schwarz
import YM.Heat.Duration
/-! Heat gap estimate with costs. No gap at zero energy assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup.Plate
open Function Filter Set Metric Complex MeasureTheory
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)(t u:ℝ≥0)
local notation "T"=> duration t
local notation "D"=> (t:ℝ)
local notation "U"=> duration (t+u)
local notation "E"=> S.E
local notation "F"=> S.F
lemma begins (v:ℂ)(p:v∈ ball T D): v∈inside:=by
 change 0<v.re; rw [mem_ball,dist_eq_norm, norm_sub_rev] at p; have he:= (re_le_norm (T-v)).trans_lt p; rw [sub_re,ofReal_re] at he; linarith -- lemma
lemma drift (h:0<t) : ‖F U-F T‖ ≤ 2*(u:ℝ) / (t:ℝ):=by
 have ht:0 < D:=h; have hu:0<t+u:=(by positivity); by_cases p:u<t
 ·
   have g:dist U T=u:=by rw [dist_eq_norm,duration,duration, NNReal.coe_add, ofReal_add, add_sub_cancel_left]; simp
   have hv:U∈ ball T D:=by rw [mem_ball,g]; exact p
   have hw := dist_le_div_mul_dist_of_mapsTo_ball (f:=F) (fun i u=>(S.localHeat i (begins t i u)).differentiableAt.differentiableWithinAt) (R₂:=2) (fun z y=> (show _ from ?_)) hv -- DifferentiableWithinAt.mono
   · rw [g,dist_eq_norm] at hw; exact hw.trans_eq (by ring)
   rw [mem_closedBall,dist_eq_norm]; refine (norm_sub_le ..).trans ?_; linarith [S.norm_row (begins t z y), S.norm_row (dur.mpr h)]
 have hh:(t:ℝ) ≤ u:=le_of_not_gt p
 refine (norm_sub_le ..).trans ((add_le_add (S.norm_row (dur.mpr hu)) (S.norm_row (dur.mpr h))).trans ?_); rw [le_div_iff₀ ht]; linarith
lemma climb (h:0<t): ‖(E t)*(E u-1)‖ ≤ 2*(u:ℝ)/(t:ℝ):=by
 have he:E t*E u=E (t+u):=(S.time ..).symm; rw [mul_sub,mul_one,he,← S.roots_heat h,← S.roots_heat (show 0<t+u by positivity)]; exact drift S t u h
lemma many_climbs (n:ℕ)(h:0<t) : ‖(E t) * (E u-1)^n‖ ≤ (2*(u:ℝ)*n/(t:ℝ))^n:=by
 by_cases p:n=0; · rw [p,pow_zero,pow_zero,mul_one]; apply S.shrinks
 have hq:0<n:=Nat.pos_of_ne_zero p; let a:ℝ≥0:=t/n; have he:0<a:=by positivity
 have hb:(E a)^n=E t:= by rw [← S.clock_mul,show n • a=t from (by rw [nsmul_eq_mul]; unfold a; field_simp)]
 have hx:Commute (E a) (E u):= by change (E a).comp _=(E u).comp _; rw [←S.time,←S.time,add_comm]
 have hy:= hx.sub_right (Commute.one_right (E a))
 rw [← hb,← hy.mul_pow]; refine (norm_pow_le' _ hq).trans (pow_le_pow_left₀ (norm_nonneg _) ((climb S a u he).trans_eq ?_) _); unfold a; rw [NNReal.coe_div,NNReal.coe_natCast]; field_simp
end YM.OS.Semigroup.Plate
#print axioms YM.OS.Semigroup.Plate.many_climbs
