import YM.SU5.FiniteGaugeData.Seld.Sault
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S: OS.Semigroup H a)(x y:H)(t:ℝ)(u:ℝ≥0)
local notation "rayA"=> Ioi (0:ℝ)
local notation "R"=> saucer S
abbrev parade (t:ℝ):H.Op:= I • (1-R)* S.edge t
lemma rope(z:ℂ)(p:z∈ inside): -I • (slug S z * R) = I • (1-R)*S.F z:=by
 let F:= S.F z; let C:=slug S z; have he:= jalousie S z p; change (F-C)*R=F at he; rw [sub_mul,← (cupF S z p).eq] at he; rw [smul_mul_assoc,neg_smul,← smul_neg,sub_mul,one_mul]; exact congrArg (I • ·) (by change -(C*R)=F-R*F; rw [eq_sub_iff_add_eq]; rw [add_comm]; exact (Eq.trans (by rw [sub_eq_add_neg] : _= R*F-C*R) he))
lemma glor (z:ℂ) (p:z∈inside) : HasDerivAt (fun t=> S.edge t (R (S.F z x))) (parade S t (S.F z x)) t:=by
 let w:=z+sideways t; have h:w∈inside:= (allow z t).mpr p
 let y: H:=R x
 have hp : HasDerivAt (fun z=> S.F z y) (slug S w y) w := (ContinuousLinearMap.apply ℂ H.space y).hasFDerivAt.comp_hasDerivAt _ (S.localHeat w h|>.differentiableAt.hasDerivAt)
 have hh : HasDerivAt (fun i:ℝ=>S.F (z+sideways i) y) (-(I:ℂ) • slug S w y) t:= convert_H _ t _ w _ _ hp (by unfold sideways; convert ((ofRealCLM.hasDerivAt (x:=t)).neg.mul_const I).const_add z using 1 <;> (first |rfl|simp)) rfl
 convert hh using 1
 · funext i; rw [show R (S.F z x)= S.F z y from DFunLike.congr_fun (cupF S z p).eq x]; exact DFunLike.congr_fun (S.along p i) y
 unfold parade; change (I • (1-R)) (S.edge t (S.F z x)) = _; rw [show S.edge t (S.F z x)= S.F w x from DFunLike.congr_fun (S.along p t) x]; exact DFunLike.congr_fun (rope S _ h).symm x
lemma together : Continuous (fun p:H×ℝ=> S.edge p.2 p.1):= continuous_prod_of_continuous_lipschitzWith _ 1 S.cont fun t=>(show Isometry (S.edge t) from AddMonoidHomClass.isometry_of_norm _ (S.life t)).lipschitz
lemma ballade : Continuous (uncurry (fun x:H=>fun t=>parade S t x)):= (show H.Op from I • (1-R)).continuous.comp (together S)
lemma music : Continuous (fun t => parade S t x):= (show H.Op from I • (1-R)).continuous.comp (S.cont x)
lemma echo : (∫ s in 0..t, parade S s x) = S.edge t (R x) - R x := by
 let f(x:H):= ∫ s in 0..t, parade S s x; let g(x:H):= S.edge t (R x) - R x
 refine congrFun ((S.whole 1).equalizer (show Continuous f from intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (ballade S) 0 t) (show Continuous g from ((S.edge t).continuous.comp (saucer S).continuous).sub (saucer S).continuous) (funext ?_)) x
 intro p; rw [← S.roots_heat (show (0:ℝ≥0)<1 from zero_lt_one)]; let v:=S.F (duration 1) p
 exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>glor S p s (duration 1) (dur.mpr zero_lt_one)) ((music S v).intervalIntegrable ..)).trans (by rw [S.birth]; rfl)
lemma fanfare : HasDerivAt (fun t=> S.edge t (R x)) (parade S t x) t:= by
 have he(t:ℝ) := (eq_sub_iff_add_eq.mp (echo S x t)).symm
 rw [funext (show ∀ t, S.edge t (R x)= _ from he)]; exact (intervalIntegral.integral_hasDerivAt_right ((music S x).intervalIntegrable ..) (music S x).stronglyMeasurable.stronglyMeasurableAtFilter (music S x).continuousAt).add_const _
#print axioms fanfare
end YM.CF.Buffered.Afterglow.Hierarchy.Seld
