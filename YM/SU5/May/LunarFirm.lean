import YM.SU5.May.LunarBand
import Mathlib.Analysis.Calculus.SmoothSeries
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical
open Window.ArchiveK Window.Largo
attribute [local instance] opCStarAlgebra lint_prob
variable {T δ:ℝ}(h:0<T) (α:ℝ)(p:δ≤1)(u:δ*δ=1)(s:coastE (α*(2* Real.pi))=(δ:ℂ))
variable (P N:E4)(ht:‖N‖=1)(hm:inner ℝ N P=0)(q:P≠0)(x:ℝ)
-- $alpha left charge
local notation "V" n:max => nodeR T α n
local notation "η" => ‖P‖
local notation "Z" i:max => (P+i • N)
local notation "Y" => Real.exp (- ‖P‖*T)
-- dialect loft; sign POS means $forward η.s$ (neg time front)
def shaft (P N:E4)(b:ℝ):Momentum:= brushQ P-(Complex.I*b) • brushQ N
def lensome (P N:E4)(b:ℝ):= leer (shaft P N b)^8
def errata (P N:E4)(b x:ℝ):= (Real.exp (b*x):ℂ)*lensome P N b
noncomputable def pillarF (P N:E4)(b x:ℝ):=coastE (x*b)*(whey ‖P‖ b:ℂ)*amiX (P+b • N)
lemma shed (i:E4)(b:ℝ): rise (shaft P N b) i= coastE (inner ℝ P i) * (Real.exp (b* inner ℝ N i):ℂ):=by
 unfold shaft rise coastE; rw [pis,pis]; push_cast; simp only [Pi.sub_apply,Pi.smul_apply,brushQ,Fir.tmap, smul_eq_mul]; rw [← Complex.exp_add]; simp_rw [sub_mul,sum_sub_distrib,mul_sub]; simp only [mul_assoc,←Finset.mul_sum]; ring_nf; simp [sub_eq_add_neg] -- crossing
lemma shed_q(i:E4)(b:ℝ):‖rise (shaft P N b) i‖= Real.exp (b* inner ℝ N i):=by rw [shed,norm_mul,coast_pay,one_mul,Complex.norm_real]; exact Real.norm_of_nonneg (Real.exp_nonneg _)
private lemma peak (i:E4)(b:ℝ): ‖rise (shaft P N b) i‖ ≤ Real.exp (|b| * ‖N‖*‖i‖) := by
 rw [shed_q]; apply Real.exp_monotone; refine (le_abs_self _).trans ?_; rw [abs_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm N i) (abs_nonneg _)
include ht in
lemma lent(b:ℝ): Integrable (fun i:Brio=> rise (shaft P N b) (foamQ i)) lintZ ∧ ‖lensome P N b‖ ≤ Real.exp (20*|b|):=by
 let C:= Real.exp (20* |b|); let l:= fun i:Brio=>rise (shaft P N b) (foamQ i); have he:∀ᵐ i ∂lintZ, ‖l i‖≤ C:= lint_cost.mono fun i t=> (peak P N (foamQ i) b).trans (Real.exp_monotone (by rw [ht,mul_one,mul_comm 20]; gcongr))
 rw [lensome,← marrow]; refine ⟨(integrable_const (μ:=lintZ) C).mono' ?_ he,(norm_integral_le_of_norm_le (integrable_const _) he).trans_eq ?_⟩
 apply Continuous.aestronglyMeasurable; exact rise_safe.comp (continuous_const.prodMk foam_cont)
 simp [C]
local notation "Bₓ" i:max => Real.exp (-(i)*T) -- ℝ
local notation "Θ" => ((fareP T ‖P‖ δ:ℝ):ℂ)
def plateF(T E δ:ℝ)(P N:E4)(x:ℝ):ℂ:= (fareP T E δ:ℂ) * (errata P N E x+ ((δ*Real.exp (-E*T):ℝ):ℂ)*errata P N (-E) x)
include h ht p s u q
lemma steady (v:-T+20<x)(w:x< -20): HasSum (fun n:ℤ=>pillarF P N (V n) x) (plateF T ‖P‖ δ P N x) := by
 let A(i:ℤ)(z:Brio):= coastE (x*(V i))* rise (brushQ (P+(V i) • N)) (foamQ z) * (whey ‖P‖ (V i):ℂ)
 let F:= (fareP T ‖P‖ δ:ℝ); let b:=δ*Y; let M(c:ℝ)(z:Brio):= coastE (inner ℝ P (foamQ z)) *(Real.exp (c*(x+inner ℝ N (foamQ z))):ℂ)
 have he (i:ℤ): pillarF P N (V i) x=∫ z:Brio, A i z ∂lintZ:=by unfold A pillarF amiX; rw [integral_mul_const, integral_const_mul,marrow]; ring
 have hc(i z): ‖A i z‖=whey ‖P‖ (V i):=by unfold A; rw [norm_mul,norm_mul,rise_real,coast_pay,coast_pay,one_mul,one_mul,norm_real]; exact Real.norm_of_nonneg (whey_p _)
 have hQ:0<η:=norm_pos_iff.mpr q
 have hZ(z): |inner ℝ N z| ≤ ‖z‖:=by rw [←one_mul ‖z‖,←ht]; exact abs_real_inner_le_norm ..
 have hz(i:ℤ): Integrable (A i) lintZ:= (integrable_const _).mono' (by apply Continuous.aestronglyMeasurable; simp_rw [A, rise_real]; fun_prop) (Eventually.of_forall fun j=> (hc i j).le) -- a bloat
 have f0 : Summable (fun i=>∫ z:Brio, ‖A i z‖ ∂lintZ):= by simp_rw [hc]; simpa only [integral_const,probReal_univ,one_smul] using stableK h hQ α
 have hm:∀ᵐ z:Brio ∂lintZ,(∑' n:ℤ,A n z)= (F:ℂ)*(M η z+(b:ℂ)*M (-η) z):=by
    filter_upwards [lint_cost] with z e; let B:=foamQ z; let u':= inner ℝ P B; let t:= inner ℝ N B; have hX : |t|≤20:= (hZ B).trans e
    have hu(n:ℤ): A n z= coastE u'* (coastE ((x+t)*(V n))*(whey η (V n):ℂ)):=by
       unfold A; rw [rise_real,inner_add_left,real_inner_smul_left]; rw [←coast_add, ←mul_assoc,←coast_add]; unfold u' t B; ring_nf
    simp_rw [hu,tsum_mul_left]; rw [(loomP h hQ α p u s (x+t) (by linarith [(abs_le.mp hX).1]) (by linarith [(abs_le.mp hX).2])).tsum_eq]; unfold F hood b M u' t B; simp only [ofReal_mul]; ring
 have h' (c:ℝ)(z:Brio): M c z= (Real.exp (c*x):ℂ) * rise (shaft P N c) (foamQ z):=by unfold M; rw [mul_add,Real.exp_add,shed, ofReal_mul]; ring
 have h_I(c:ℝ): Integrable (M c) lintZ:=by rw [funext (h' c)]; exact (lent P N ht c).1.const_mul _
 have hQ:(∫ z:Brio,(∑' n:ℤ,A n z)∂lintZ)= plateF T ‖P‖ δ P N x:=by rw [integral_congr_ae hm, integral_const_mul, integral_add (h_I η) ((h_I _).const_mul _),integral_const_mul]; simp_rw [h',integral_const_mul,marrow]; rfl
 rw [←hQ]; simp_rw [he]; exact hasSum_integral_of_summable_integral_norm hz f0
#print axioms steady
end YM.CF.May.Lunar
