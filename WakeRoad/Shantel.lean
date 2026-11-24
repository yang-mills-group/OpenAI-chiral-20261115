import WakeRoad.Four
import YM.SU5.WakeInvestment.FinalScene
/-! # Scoring polynomial consultations in Brooms. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace YM.WakeRoad
open Function Filter Metric Finset NormedSpace MeasureTheory ProbabilityTheory
open YM.SU5.FiniteGaugeData.Indigo Sweat
open scoped Topology RealInnerProductSpace BigOperators NNReal ENNReal ContDiff Classical
set_option quotPrecheck false
variable {I:Type}[Fintype I]
abbrev Press (I:Type):= I → I →ℂ
variable (T:Press I)
/- counsel homogeneous lines -/
def Score (x:I→ℝ):ℂ:=∑ i:I,∑ j:I, (x i*x j) • T i j
def coin :ℝ:=∑ i:I,∑ j:I, ‖T i j‖
lemma coin0: 0≤ coin T:= sum_nonneg fun _ _=> sum_nonneg fun _ _=> norm_nonneg _
lemma score_scale (x:I→ℝ)(c:ℝ): Score T (c • x)=c^2 • Score T x:=by unfold Score; simp only [Finset.smul_sum,smul_smul, Pi.smul_apply,smul_eq_mul, pow_two]; ring_nf
-- hard max order m=2 diff with constant 2 loss.
lemma score_pay (x:I→ℝ) (B:ℝ)(p:∀i,|x i|≤ B)(h:0≤B): ‖Score T x‖ ≤ coin T * B^2:=by
 unfold Score coin; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_); rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_) ; rw [norm_smul,Real.norm_eq_abs,abs_mul,pow_two,mul_comm (norm _)]; gcongr; exacts [p _,p _]
lemma score_equate (x y:I→ℝ) {B d:ℝ}(p:∀i,|x i| ≤B)(v:∀ i,|y i| ≤B)(h:0≤B)(q:∀i, |x i - y i|≤d): ‖Score T x-Score T y‖ ≤ 2*coin T*B*d:=by
 unfold Score; rw [← Finset.sum_sub_distrib];simp_rw [←Finset.sum_sub_distrib,←sub_smul]
 have g:2*coin T * B*d=∑ i:I,∑ j:I,(2*B*d) *‖T i j‖:=by unfold coin; simp_rw [←Finset.mul_sum]; ring
 rw [g]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=> ?_)); rw [norm_smul,Real.norm_eq_abs]
 apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 rw [show x i*x j-y i*y j=(x i-y i)*x j+y i*(x j-y j) by ring]; apply (abs_add_le ..).trans; simp only [abs_mul]; have h0:0 ≤ d:= (abs_nonneg _).trans (q i)
 have ht: d*B+B*d= 2*B*d:=by ring
 exact (add_le_add (mul_le_mul (q i) (p j) (abs_nonneg _) h0) (mul_le_mul (v i) (q j) (abs_nonneg _) h)).trans ht.le
lemma score_sol: Regis.Wake.Paint (Score T) 2 (2*coin T) := by
 constructor
 · unfold Score; fun_prop
 · intro B t x h
   have hv:coin T ≤ 2*coin T:=by linarith [coin0 T]
   exact (score_pay _ x _ (fun i=> (norm_le_pi_norm ..).trans h) (zero_le_one.trans t)).trans (by gcongr)
 intro B a x y h w
 refine (score_equate _ _ _ (fun i=> (norm_le_pi_norm x i).trans h) (fun i=> (norm_le_pi_norm y i).trans w) (zero_le_one.trans a) (fun i=> norm_le_pi_norm (x-y) i)).trans ?_
 gcongr; · exact mul_nonneg (by norm_num) (coin0 _)
 simpa only [pow_two] using (le_mul_of_one_le_right (zero_le_one.trans a) a)

def review(i j:I):ℂ := (1/2:ℝ) • (T i j+T j i)
lemma review_paid: coin (review T) ≤ coin T:= by
 unfold coin review; simp_rw [norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ) ≤ 1/2)]
 refine (sum_le_sum (fun i _=> sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (norm_add_le ..) (by norm_num : (0:ℝ) ≤ 1/2))).trans ?_
 simp_rw [←Finset.mul_sum,Finset.sum_add_distrib]; rw [sum_comm]; linarith
lemma revised(x:I→ℝ): Score (review T) x = Score T x:=by
 unfold Score review; simp_rw [smul_comm (_* _:ℝ) (1/2:ℝ), smul_add,Finset.sum_add_distrib]
 simp_rw [← Finset.smul_sum]
 rw [show (∑ i:I, ∑ j:I,(x i*x j) • T j i) =(∑ i:I, ∑ j:I,(x i*x j) • T i j) from ?_]
 swap; · rw [sum_comm]; congr 1; funext i; apply sum_congr rfl fun j _=>?_ ; rw [mul_comm (x j)]
 rw [← add_smul]; norm_num
omit [Fintype I] in
@[simp] lemma revision (i j:I): review T j i=review T i j:=by simp [review,add_comm]
#print axioms revised
