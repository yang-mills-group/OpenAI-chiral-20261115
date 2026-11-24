import Acacia.Amen
import HectorA.InShift
import Acacia.Rill
import Acacia.Smith
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace Acacia
open Filter Function Finset Set YM.OS YM Yoland
open scoped Topology NNReal BigOperators Classical InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
/-- ℝ→op→κ layout F. y offsets. -/
def contractD (x y:H)(T:H.Op) :H.Op→L[ℝ] ℂ:=
 ((innerSL ℂ x).comp (T.comp (ContinuousLinearMap.apply ℂ H.space y))).restrictScalars ℝ
lemma contract_correct(x y:H)(T D:H.Op):contractD x y T D=inner ℂ x (T (D y)):=rfl
lemma contract_paid(x y:H)(T D:H.Op)(p:‖T‖≤1): ‖contractD x y T D‖ ≤ (‖x‖*‖y‖)*‖D‖:=by
 rw [contract_correct]; apply (norm_inner_le_norm x _).trans
 rw [mul_assoc, mul_comm ‖y‖]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 exact (T.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) p).trans (D.le_opNorm _))
variable (F:ℝ→ℂ){V:Type*}(n:ℕ)(x y:H)(T:H.Op)
/-- For q-axis purchases where q real; representation over t.E uniform beyond M.
 t parameter now offset about second.Arg.
-/
lemma esteem(t:ℝ)(v:0<t) (u:F =ᶠ[𝓝 0] (fun i:ℝ=> inner ℂ x (T (dawn S (t+i) y)))):
 iteratedDeriv n F 0= inner ℂ x (T ((pay S n t) y)):=by
 let f(i):= dawn S (t+i); let L:=contractD x y T
 have hL:AnalyticAt ℝ f 0:= (show AnalyticAt ℝ (dawn S) (t+0) from by rw [add_zero]; exact dawnRise S t v).comp (f:=fun i:ℝ=>t+i) (analyticAt_const.add analyticAt_id)
 exact (u.iteratedDeriv_eq n).trans ((transport hL L n).trans (congrArg L (show iteratedDeriv n f 0= pay S n t from by unfold f pay; simp only [iteratedDeriv_comp_const_add,add_zero]) : _=inner ℂ x (T ((pay S n t) y))))
lemma delta_shift{X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X](n:ℕ)(f:ℝ→X)(h r t:ℝ):delta h n (fun i:ℝ=>f (t+i)) r=delta h n f (t+r):=by
 induction n generalizing r with
 | zero=>rfl
 | succ n ih=>rw [delta_s,delta_s,ih,ih,add_assoc]
lemma crema_step(t:ℝ)(h:ℕ→ℝ): ∀ i:ℕ, delta (h i) n (fun z=>inner ℂ x (T ((dawn S (t+z)) y))) 0= contractD x y T (delta (h i) n (dawn S) t):=by
 intro i
 let f(z:ℝ):= dawn S (t+z)
 refine congrFun (delta_clm (h i) n (contractD x y T) f) 0 |>.trans ?_
 apply congrArg (contractD x y T); rw [show delta (h i) n f 0= _ from delta_shift n (dawn S) _ 0 t,add_zero]
-- exact bill on n. select t:=t/(n+1), way
lemma cuppa(t:ℝ)(v:0<t)(h:ℕ→ℝ)(hc:∀i,0 < h i)(hg:Tendsto h atTop (𝓝 0)):
 ∃ C:ℝ, 0<C∧∀ᶠ i:ℕ in atTop,∀ T:H.Op, ‖T‖≤1→ ‖delta (h i) n (fun z:ℝ=>inner ℂ x (T ((dawn S (t+z)) y))) 0-inner ℂ x (T ((pay S n t) y))‖ ≤ h i*C:=by
 let u:=t/((n:ℝ)+1); have hu:0<(n:ℝ)+1:=by positivity
 obtain ⟨A,k,e⟩:= way S hc u (div_pos v hu) hg t n (show (n:ℝ)*u≤t from (by unfold u; rw [← mul_div_assoc,div_le_iff₀ hu]; linarith))
 let d:=‖x‖*‖y‖; refine ⟨(d+1)*A, by unfold d; positivity,?_⟩
 filter_upwards [e] with i c; intro T p
 have hz:0≤d:=mul_nonneg (norm_nonneg _) (norm_nonneg _); let D:=delta (h i) n (dawn S) t
 rw [crema_step S n x y T t h,← contract_correct,←map_sub]
 exact (contract_paid _ _ _ _ p).trans ((mul_le_mul_of_nonneg_left c hz).trans (by change d*(h i*A) ≤_; nlinarith [hc i]))
#print axioms cuppa
#print axioms esteem
end Acacia
