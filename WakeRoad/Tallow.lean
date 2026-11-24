import WakeRoad.Saplings
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
variable (T:Press I)
/- counsel homogeneous lines -/
variable {J:Type}[Fintype J][DecidableEq J]
open CF.Buffered.Afterglow.Tower.VacuumSelection.GramSignal

def tinV (F:I→J)(d:J)(i:I):ℂ:=if F i=d then 1 else 0
def compact (F:I→J)(E:Press I)(x y:J):ℂ:=∑i:I,∑j:I,tinV F x i * tinV F y j * E i j
-- diagonal leading. maybe calculate avoiding if orientation symmetry estimator
lemma compass_score (F:I→J)(x:J→ℝ) : Score T (fun i=>x (F i))=Score (compact F T) x:=by
 unfold Score compact; symm
 simp_rw [Finset.smul_sum, sum_comm (t:=univ (α:=I)) (s:=univ (α:=J))]
 apply sum_congr rfl (fun i _=> sum_congr rfl fun j _=>?_)
 unfold tinV; simp [Complex.real_smul]

omit [Fintype J] in
lemma compact_sym (F:I→J)(h:∀i j,T i j=T j i)(x y:J):compact F T x y=compact F T y x:=by
 unfold compact; rw [sum_comm]; exact sum_congr rfl fun j _=> sum_congr rfl fun i _=> by rw [h i j];ring

def pattern (F:I→J)(x y:I):ℂ:=if F x=F y then 1 else 0
lemma affinity_cash (P:I→J)(V: Press I) (h:∀i j,T i j=T j i):
 affinity (pattern P) V T= 2*∑i:J,∑j:J,compact P V i j * compact P T i j :=by
 unfold affinity
 have e(i j:I): (∑ t:I,∑l:I, V i j * T t l * (pattern P t i*pattern P l j+pattern P l i*pattern P t j))=2*(∑t:I,∑l:I,V i j*T t l*(pattern P t i*pattern P l j)):=by
    simp_rw [_root_.mul_add,Finset.sum_add_distrib,two_mul]; congr 1; rw [sum_comm]; apply sum_congr rfl; intro k _; apply sum_congr rfl; intro p _; rw [h p k]
 simp_rw [e,←Finset.mul_sum]; congr 1; unfold compact; simp_rw [Finset.sum_mul,Finset.mul_sum,sum_comm (s:=univ (α:=J)) (t:=univ (α:=I))]; -- order right from sum? 
 -- `mul_sum` simp before `sum_mul` puts T compact indices outermost because simp rewrites root. inspect
 apply sum_congr rfl fun i _=>sum_congr rfl fun j _=>sum_congr rfl fun a _=>sum_congr rfl fun b _=>?_
 unfold tinV pattern; simp [ite_mul,mul_ite,eq_comm] -- simp sum
#print axioms affinity_cash
private lemma abs_normsq (c:ℂ) : star c*c=(↑(‖c‖^2:ℝ):ℂ):= by rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.sq_norm]
lemma favor (P:I→J)(h:∀i j,T i j=T j i): affinity (pattern P) (fun i j=>star (T i j)) T=(2* (↑(∑i:J,∑j:J,‖compact P T i j‖^2 :ℝ):ℂ)):=by
 rw [affinity_cash T P _ h]; push_cast; congr 1
 refine sum_congr rfl fun i _ => sum_congr rfl fun j _=>?_ ; rw [← Complex.ofReal_pow,← abs_normsq]; unfold compact; simp only [star_sum,star_mul]; refine congrArg (·*(∑ i',∑ j',tinV P i i'*tinV P j j'*T i' j')) (sum_congr rfl fun v _=>sum_congr rfl fun x _=>?_)
 unfold tinV; split_ifs <;> simp

-- signing the covariance kernel exactly cancels reflection effect
omit [Fintype J] in
lemma mirror_pay (P:I→J)(t:I→ℝ)(h:∀i,|t i|=1)(k:ℝ)(W:Press I):
 affinity (fun i j=>(k:ℂ) * t j * pattern P i j) (fun i j=> (t i*t j) • W i j) T= (k^2:ℝ) • affinity (pattern P) W T :=by
 unfold affinity; simp_rw [Finset.smul_sum]; apply sum_congr rfl fun i _=> sum_congr rfl fun j _=> sum_congr rfl fun a _=> sum_congr rfl fun b _=> ?_
 have h'(x:I): ((t x:ℝ):ℂ)*((t x:ℝ):ℂ)=1:=by
    exact_mod_cast (show t x *t x=1 from (abs_mul_abs_self _).symm.trans (by rw [h x]; ring))
 rw [Complex.real_smul,Complex.real_smul]; push_cast
 calc _ = (((t i:ℝ):ℂ)*t i)*(((t j:ℝ):ℂ)*t j)*((k:ℂ)^2 * (W i j*T a b*(pattern P a i*pattern P b j+pattern P b i*pattern P a j))) := by ring
      _ = _:=by rw [h',h']; ring
#print axioms mirror_pay
-- normalization ONE priority test yields lower for E. just finite fixed dimension.
omit [DecidableEq J] in
lemma glitter (v:J→ℝ)(δ:ℝ)(hδ:0<δ): ∃ p:ℝ, 0<p ∧ ∀ (T:Press J),δ ≤ ‖Score T v‖→ p^2 < ∑ i:J,∑ j:J,‖T i j‖^2:=by
 let l:=(Fintype.card J:ℝ); have hl:0≤l:= Nat.cast_nonneg _
 let Y:=∑ i:J,∑ j:J,|v i*v j|
 have hy: 0 ≤ Y:= sum_nonneg fun _ _=>sum_nonneg fun _ _=> abs_nonneg _ -- unused
 let p:=δ/(Y+1); have hp :0<p:=by unfold p; positivity
 refine ⟨p,hp,fun T h=>?_⟩
 have h':∃ i:J,∃ j:J,p < ‖T i j‖:=by
    by_contra! t; apply not_lt_of_ge h; unfold Score; refine lt_of_le_of_lt (norm_sum_le ..) (lt_of_le_of_lt (sum_le_sum (g:=fun i:J=>∑ j:J,|v i *v j| *p) (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun j _=>?_)))) ?_)
    · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (t i j) (abs_nonneg _)
    simp_rw [← Finset.sum_mul]; change Y*p<δ; calc
      _ < (Y+1)*p:=by nlinarith only [hp]
      _ = δ:=by unfold p; field_simp
 obtain ⟨i,j,t⟩:=h'; refine (sq_lt_sq₀ hp.le (norm_nonneg _)|>.mpr t).trans_le ?_
 exact (single_le_sum (fun i' _=> sq_nonneg (‖T i i'‖)) (mem_univ j)).trans (single_le_sum (f:=fun i'=>∑ j,‖T i' j‖^2) (fun i' _=> sum_nonneg fun j _=>sq_nonneg _) (mem_univ i))

lemma lateral (U P Q:Press I) (C e:ℝ)(h:∀i j,‖P i j-Q i j‖≤ e)
    (t:∀ i j,‖P i j‖ ≤ C)(v:∀ i j,‖Q i j‖ ≤ C):
 ‖affinity P U T - affinity Q U T‖ ≤ coin U * coin T * (4*C*e):=by
 have x(i j k l:I):‖P i j* P k l - Q i j*Q k l‖ ≤ 2*C*e :=by
    have v':0≤e:= (norm_nonneg _).trans (h i j)
    rw [show P i j* P k l - Q i j*Q k l=(P i j-Q i j)*P k l+ Q i j*(P k l-Q k l) by ring]; apply (norm_add_le ..).trans; simp only [norm_mul]; refine (add_le_add (mul_le_mul (h i j) (t k l) (norm_nonneg _) v') (mul_le_mul (v i j) (h k l) (norm_nonneg _) ((norm_nonneg _).trans (v i j)))).trans_eq ?_; ring
 unfold affinity coin; simp_rw [←sum_sub_distrib,sum_mul,mul_sum,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (fun j _=> (norm_sum_le ..).trans (sum_le_sum (fun a _=> (norm_sum_le ..).trans (sum_le_sum (fun b _=>?_))))))))
 rw [←mul_sub,norm_mul,norm_mul,show P a i*P b j+P b i*P a j-(Q a i*Q b j+Q b i*Q a j)=(P a i*P b j-Q a i*Q b j)+(P b i*P a j-Q b i*Q a j) by ring]
 apply mul_le_mul_of_nonneg_left _ (by positivity); apply (norm_add_le ..).trans; exact (add_le_add (x ..) (x ..)).trans_eq (by ring)
#print axioms glitter
#print axioms lateral
