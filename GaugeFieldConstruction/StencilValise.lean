import YM.SU5.FiniteGaugeData.Seld.WildCat
import YM.SU5.SatinWard.Resolution.Lamina

/-!
# Comparing the symmetrically padded operators
Time derivative is diffusing in both lags and is brought to the harmonic-price rule. Spatial
symmetry does NOT come by assuming a Lorentz move respects either pricing. For a charged (hence
norm differentiable) spatial move we use integration by parts in actual E4 smearing of a padded
reading.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)
open Spectral Boundary Probe Gear
variable (A B:H.Op)(x y:H)(g:Test4)
local notation "V" => optx S

lemma val_space (v:E4)(h:HasDerivAt (fun z:ℝ=>optx S A (z • v)) B 0) :
 valise S B g = valise S A (-(shade v g)):=by
 ext1 y; apply ext_inner_left ℂ; intro x
 let f:=shade v g
 let d(p:E4) := lucent S x y A p; let z(p:E4):= lucent S x y B p
 have hp(p:E4): HasLineDerivAt ℝ d (z p) p v := by
    unfold HasLineDerivAt
    have ht:(fun u:ℝ=>V A (p+u • v))=(fun u:ℝ=> M S p*V A (u • v)* M S (-p)):=funext (fun u=> (opt_act S p _ A).symm)
    have hx: HasDerivAt (fun u:ℝ=>V A (p+u • v)) (V B p) 0:=by
       rw [ht]; exact (h.const_mul _).mul_const _
    exact ((innerSL ℂ x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ (((ContinuousLinearMap.apply ℂ H.space y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ hx)
 have he:(∫ p,g p*z p)= -(∫ p,f p*d p):= integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B:=ContinuousLinearMap.mul ℝ ℂ) (sell S x y A f) (sell ..) (sell ..) (fun p _=>shadeD v g p) (fun p _=>hp p)
 rw [show valise S A (-(shade v g)) = -(valise S A f) from map_neg (barren S A) f]
 change inner ℂ _ _= inner ℂ x (- valise S A f y); rw [inner_neg_right,←sell_in,← sell_in]; exact he
variable (T:ℝ→ℝ→ H.Op)(K:S.Credits 0 T)
include K
lemma baryTime (t s:ℝ≥0)(h:0<s)(p:s+s=t):
  deriv (currentTemp T t t) 0= deriv S.F (duration s)*T s s*S.E s-S.E s*T s s*deriv S.F (duration s):=by
 let X:=T s s; let U(p:ℝ):= S.wax ((s:ℝ)+p); let W(p:ℝ):= S.wax ((s:ℝ)-p)
 let B:=deriv S.F (duration s); have u: U 0=S.E s:=by unfold U wax; rw [add_zero,Real.toNNReal_coe]
 have w: W 0=S.E s:=by unfold W wax; rw [sub_zero,Real.toNNReal_coe]
 have hs:0<(s:ℝ):=h
 have hp:(s:ℝ)+s=(t:ℝ):=congrArg ((↑):ℝ≥0→ℝ) p
 have hU:HasDerivAt U B 0:=by
    have he:= (S.wax_deriv (show 0<(s:ℝ)+0 from by simpa using hs)).scomp 0 ((hasDerivAt_id' 0).const_add (s:ℝ)); rw [add_zero (s:ℝ),one_smul] at he; exact he
 have hW:HasDerivAt W (-B) 0:=by
    have he:= (S.wax_deriv (show 0<(s:ℝ)-0 from by simpa using hs)).scomp 0 ((hasDerivAt_id' 0).const_sub (s:ℝ)); rw [sub_zero,neg_one_smul] at he; exact he
 have he: HasDerivAt (fun p=> U p*X*W p) (B*X*S.E s-S.E s*X*B) 0:=by
    have hx:= (hU.mul_const X).mul hW; rw [u,w, mul_neg,←sub_eq_add_neg] at hx; exact hx
 apply HasDerivAt.deriv (he.congr_of_eventuallyEq ?_)
 filter_upwards [lt_mem_nhds (neg_lt_zero.mpr hs),gt_mem_nhds hs] with x u w
 change currentTemp T t t x=U x*X*W x; rw [currentTemp,K hs hs (by linarith only [hp,(show -(s:ℝ)<x from u)]) (by linarith only [hp,(show x<(s:ℝ) from w)])]; unfold U W X; rw [sand,show (t:ℝ)+x-s=(s:ℝ)+x from (by linarith only [hp]), show (t:ℝ)-x-s=(s:ℝ)-x from (by linarith only [hp])]
#print axioms val_space
#print axioms baryTime
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
end
