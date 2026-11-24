import WakeRoad.Spread
import YM.SU5.FiniteGaugeData.Indigo.Sweat
/-! # Fourth polarization on the stamen -/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.WakeRoad
open Function Filter Metric Finset NormedSpace MeasureTheory ProbabilityTheory
open YM.SU5.FiniteGaugeData.Indigo Sweat
open scoped Topology RealInnerProductSpace BigOperators NNReal ENNReal ContDiff Classical
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
local notation "μ"=> stdGaussian E
variable (x y z w:E)
private abbrev Y(x v:E):= inner ℝ x v
private def V (x y z w:E)(v:E):= Y x v*Y y v*Y z v*Y w v
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma polar : V x y z w = (1/4:ℝ) • (( (fun u=> cents (x+y) u*cents (z+w) u) - (fun u=> cents x u*cents (z+w) u + cents y u*cents (z+w) u))-(fun u=>cents (x+y) u*cents z u-cents x u*cents z u-cents y u*cents z u)-(fun u=> cents (x+y) u*cents w u-cents x u*cents w u-cents y u*cents w u)):=by ext v; simp only [Pi.smul_apply,Pi.sub_apply,V,cents,Y,inner_add_left,smul_eq_mul]; ring
lemma moments : Integrable (fun v=> inner ℝ x v * inner ℝ y v * inner ℝ z v * inner ℝ w v) μ ∧ (∫ v:E, inner ℝ x v * inner ℝ y v * inner ℝ z v * inner ℝ w v ∂ μ) = inner ℝ x y*inner ℝ z w + inner ℝ x z*inner ℝ y w+inner ℝ x w*inner ℝ y z := by
 change Integrable (V x y z w) μ ∧ (∫ v,V x y z w v∂μ)=_; let f (x y v:E):=cents x v*cents y v
 have h (x y:E): Integrable (f x y) μ:=cashV x y
 let S(x y a:E):= f (x+y) a-f x a-f y a; have hs(x y a:E): Integrable (S x y a) μ:= ((h (x+y) _).sub (h x _)).sub (h y _)
 rw [polar, show ( (fun u=> cents (x+y) u*cents (z+w) u) - (fun u=> cents x u*cents (z+w) u + cents y u*cents (z+w) u))=S x y (z+w) from (funext fun v=>sub_add_eq_sub_sub ..)];
 change Integrable _ μ ∧ (∫ v, _ ∂ μ)= _; let R:= S x y (z+w) - S x y z-S x y w; have he: Integrable R μ:= ((hs x y _).sub (hs x y z)).sub (hs x y w)
 refine ⟨he.smul _,?_⟩
 let F(i:E→ℝ):=∫ v:E,i v∂ μ
 have hp(x y:E): F (f x y)=_:= WickQ x y
 have hf(a:E): F (S x y a)= 2*inner ℝ x y*‖a‖^2+4*inner ℝ x a*inner ℝ y a:=by
    unfold F S; change (∫ v:E,f (x+y) a v-f x a v-f y a v∂ μ)=_; erw [integral_sub ((h (x+y) a).sub (h x a)) (h y a),integral_sub (h (x+y) a) (h x a)]; unfold F at hp; rw [hp,hp,hp,norm_add_sq_real,inner_add_left]; ring
 change (∫ v:E,(1/4:ℝ) • R v∂ μ)=_; rw [integral_smul]; unfold R; simp only [Pi.sub_apply]; erw [integral_sub ((hs x y _).sub (hs x y z)) (hs x y w),integral_sub (hs x y _) (hs x y z)]; unfold F at hf; rw [hf,hf,hf,norm_add_sq_real,inner_add_right,inner_add_right,smul_eq_mul]; ring
#print axioms moments
end YM.WakeRoad
