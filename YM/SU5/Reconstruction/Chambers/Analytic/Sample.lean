import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# From uniform separate analytic prices to actual simultaneous complex neighborhoods.

Will use equidistant interpolation off an *interval*. Exponential price only in the
order if the target complex disc is comparable to this radius. By allowing a very
small interval, combine with larger one-dimensional analytic extensions and telescope.
No continuation from unrelated imaginary directions needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.PolyDisc.Revival
open Function Complex Filter Topology Set Metric Polynomial
open scoped BigOperators NNReal ENNReal
namespace Sample
variable {f : ℂ→ℂ} (x d : ℝ) (n : ℕ)

def W (d : ℝ) (n : ℕ) : ℝ := d/(n+1)
def points (i : ℕ) : ℝ := x+W d n*i
def nodes (i : ℕ) : ℂ := (points x d n i:ℝ)

local notation "T" => points x d n
local notation "Z" => nodes x d n
local notation "R₀" n:max => Finset.range (n+1)
local notation "A" => (Finset.range (n+1))

variable {x d n}
lemma width (g : 0<d) (n) : 0<W d n := div_pos g (by positivity)
variable (x n)
lemma room (g : 0<d) : Injective (nodes x d n) := by
  refine fun a b h => ?_
  apply Nat.cast_injective (R:=ℝ)
  refine mul_left_cancel₀ (width g n).ne' ?_
  exact add_left_cancel (ofReal_injective h)

lemma node_inner {i : ℕ} (h : 0<d) (p : i∈ Finset.range (n+1)) :
    T i∈ closedBall x d := by
  rw [mem_closedBall,Real.dist_eq,points, abs_le]
  have t : 0< W d n := width h n
  have p' : W d n*(n+1)=d := div_mul_cancel₀ _ (by positivity)
  have ht:(i:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp p))
  constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) i]

lemma complex_inner {i} (h:0<d)(p:i∈ Finset.range (n+1)) : Z i∈ closedBall (x:ℂ) d := by
  unfold nodes; rw [mem_closedBall, dist_eq_norm, ← ofReal_sub,norm_real,← dist_eq_norm]; exact node_inner x n h p

-- 1-d interpolation operator. Estimate from absolute samples and spacings.
variable (d)
def weights (i : ℕ) (z : ℂ) : ℂ := eval z (Lagrange.basis A Z i)
noncomputable def poly (f : ℂ→ℂ) := Lagrange.interpolate A Z (f ∘ Z)
lemma poly_eval (f : ℂ→ℂ) (z:ℂ) : (poly x d n f).eval z=∑ i∈A, weights x d n i z * f (Z i) := by
  simp_rw [poly,Lagrange.interpolate_apply,eval_finsetSum,weights,eval_mul,eval_C,Function.comp_apply]
  refine Finset.sum_congr rfl fun i _=> mul_comm _ _
lemma ifPol (g : 0<d) (P : Polynomial ℂ) (h : P.degree < (Finset.range (n+1)).card) : poly x d n P.eval=P := (Lagrange.eq_interpolate ((room _ _ g).injOn) h).symm -- notation eval P? flipped by dot

lemma weights_formula (i : ℕ) (z : ℂ) : weights x d n i z =
    (∏ j ∈ (A).erase i,(z-Z j)) / ∏ j ∈ (A).erase i,(Z i-Z j) := by
  unfold weights Lagrange.basis Lagrange.basisDivisor; rw [eval_prod]; simp_rw [eval_mul, eval_sub, eval_X, eval_C, Finset.prod_mul_distrib]
  rw [Finset.prod_inv_distrib, div_eq_inv_mul]

variable {d n}(g : 0<d)
include g

private lemma gaps_prod(i:ℕ)(h:i∈ Finset.range (n+1)) : (∏ j ∈ (A).erase i, ‖Z i-Z j‖)=
    (W d n)^n * (i.factorial:ℝ)*(n-i).factorial := by
  have he(j:ℕ) : ‖Z i-Z j‖= W d n * |(i:ℝ)-j| := by
    unfold nodes points; rw [← ofReal_sub, norm_real,Real.norm_eq_abs]; rw [show x+ _ - (x+ _) = W d n*((i:ℝ)-j) by ring,abs_mul,abs_of_pos (width g n)]
  simp_rw [he,Finset.prod_mul_distrib]
  rw [Finset.prod_const, Finset.card_erase_of_mem h, Finset.card_range, Nat.add_sub_cancel]
  rw [mul_assoc]; congr 1
  have v:= Finset.mem_range.mp h
  -- fix i, induct in n to simplify
  apply stored n (by omega)
where
 stored (n:ℕ)(p:i ≤ n) : (∏ j ∈ (Finset.range (n+1)).erase i, |(i:ℝ)-j|)=(i.factorial:ℝ)*(n-i).factorial := by
  induction n,p using Nat.le_induction with
  | base =>
    rw [Finset.range_add_one, Finset.erase_insert (by simp),Nat.sub_self]; norm_num
    rw [← Nat.descFactorial_self,Nat.descFactorial_eq_prod_range]; push_cast
    exact Finset.prod_congr rfl fun a h => by have h:= Finset.mem_range.mp h; rw [Nat.cast_sub h.le, abs_of_nonneg (by exact sub_nonneg.mpr (by exact_mod_cast h.le))]
  | succ n t ih =>
    rw [Finset.range_add_one, Finset.erase_insert_of_ne (by omega : n+1≠i), Finset.prod_insert (by simp), ih,
      show n+1-i=n-i+1 by omega, Nat.factorial_succ]; push_cast [Nat.cast_sub t]
    rw [abs_of_nonpos (by have h:(i:ℝ)≤ n:=(by exact_mod_cast t); linarith)]; ring

-- use coarse constant 64. valid even n=0. no log estimates needed.
lemma cost_weight {i} (h:i∈ Finset.range (n+1)){z:ℂ} (p : z∈closedBall (x:ℂ) d) :
    ‖weights x d n i z‖ ≤ (32:ℝ)^(n+1) := by
  have ht : (∏ j ∈ (A).erase i, ‖z - Z j‖) ≤ (2*d)^n := by
    have he := Finset.card_erase_of_mem h
    rw [show (2*d)^n = ∏ _j∈(A).erase i,2*d by rw [Finset.prod_const,he,Finset.card_range,Nat.add_sub_cancel]]
    apply Finset.prod_le_prod (by intros; positivity)
    intro j hj; rw [← dist_eq_norm]; exact (dist_triangle z (x:ℂ) _).trans (add_le_add (Metric.mem_closedBall.mp p) (Metric.mem_closedBall'.mp (complex_inner x n g (Finset.mem_erase.mp hj).2)) |>.trans (le_of_eq (two_mul d).symm))
  have w := width g n
  rw [weights_formula,norm_div, norm_prod, norm_prod,gaps_prod x g i h]
  apply le_trans (div_le_div_of_nonneg_right ht (by positivity))
  have h' : i ≤ n:= Nat.le_of_lt_succ (Finset.mem_range.mp h)
  have hx : ((n.choose i:ℝ)*(i.factorial:ℝ)*(n-i).factorial)=(n.factorial:ℝ) := by exact_mod_cast (Nat.choose_mul_factorial_mul_factorial h')
  have hw: (n.choose i:ℝ)≤ 2^n := by exact_mod_cast (Nat.choose_le_two_pow n i)
  have c : (n+1:ℝ)^n / (n.factorial:ℝ) ≤ 3^(n+1) := by
    refine (Real.pow_div_factorial_le_exp ((n:ℝ)+1) (by positivity) n).trans ?_
    rw [show (n:ℝ)+1 = ((n+1:ℕ):ℝ)*1 by simp, Real.exp_nat_mul]; gcongr; exact Real.exp_one_lt_three.le
  calc
    _ = 2^n * ((n+1:ℝ)^n / (n.factorial:ℝ))*(n.choose i:ℝ) := by unfold W; rw [← hx,div_pow, mul_pow]; have he : (0:ℝ)< (n.choose i:ℝ) := (by exact_mod_cast (Nat.choose_pos h')); field_simp
    _ ≤ 2^n * (3:ℝ)^(n+1)*2^n := by gcongr
    _ ≤ (2^(n+1)* (3:ℝ)^(n+1)*2^(n+1)) := by gcongr <;> norm_num
    _ ≤ _ := by rw [← mul_pow,←mul_pow]; gcongr; norm_num

lemma cost_sum (n : ℕ){z:ℂ}(p : z∈closedBall (x:ℂ) d) : (∑ i∈ Finset.range (n+1),‖weights x d n i z‖) ≤ (64:ℝ)^(n+1) := by -- A binding shadow issue
  refine (Finset.sum_le_sum (fun i t=> cost_weight x (n:=n) (i:=i) g t p)).trans ?_
  rw [Finset.sum_const, Finset.card_range,nsmul_eq_mul,Nat.cast_add_one]
  have he (n : ℕ): (n:ℝ)+1 ≤ (2:ℝ)^(n+1) := by induction n with |zero=>norm_num|succ n ih=>push_cast; rw [pow_succ' _ (n+1)]; linarith
  refine (mul_le_mul_of_nonneg_right (he _) (by positivity)).trans (le_of_eq ?_)
  rw [← mul_pow]; norm_num

section approx
-- Truncation polynomial. Need uniform exponential on all smaller boxes for any
-- extensions with a common bound. c=d/r, can make arbitrarily small.
variable {r M : ℝ}{f : ℂ→ℂ} (d) (n)
def nearT (f : ℂ→ℂ) (n : ℕ) : Polynomial ℂ := ∑ i∈ Finset.range (n+1),
  C ((i.factorial:ℂ)⁻¹*iteratedDeriv i f x)*(X-C (x:ℂ))^i
omit g in
lemma near_degree (f : ℂ→ℂ) (n : ℕ) : (nearT x f n).degree < ↑(Finset.range (n+1)).card := by
  unfold nearT; rw [← mem_degreeLT]; refine (degreeLT ..).sum_mem ?_
  intro i h; rw [mem_degreeLT, Finset.card_range]; rw [degree_mul]
  apply lt_of_le_of_lt (add_le_add_left degree_C_le _)
  rw [zero_add,degree_pow,degree_X_sub_C]; simp only [nsmul_eq_mul,mul_one]
  exact_mod_cast Finset.mem_range.mp h

omit g in
lemma near_eval (f : ℂ→ℂ) (n : ℕ)(z:ℂ) : (nearT x f n).eval z = ∑ i∈ Finset.range (n+1), (i.factorial:ℂ)⁻¹ • (z-(x:ℂ))^i • iteratedDeriv i f x := by
  simp_rw [nearT,eval_finsetSum,eval_mul,eval_pow,eval_sub,eval_X,eval_C,smul_eq_mul]
  apply Finset.sum_congr rfl fun i _=>?_ ; ring

-- boundary DifferentiableOn assumptions packaged. use y inside closed smaller disc.
variable {x n}
variable (p : d<r) (u : DiffContOnCl ℂ f (ball (x:ℂ) r)) (v : ∀ z∈ sphere (x:ℂ) r, ‖f z‖≤ M) (e : 0 ≤ M)
include u v g e p

omit e in
lemma taylor_price (n : ℕ) (z : ℂ) (h : z∈closedBall (x:ℂ) d) :
    ‖f z-(nearT x f n).eval z‖ ≤ (d/r)^(n+1) * (1-d/r)⁻¹ * M := by
  rw [near_eval]
  let F(i:ℕ):ℂ:= (i.factorial:ℂ)⁻¹ • (z-(x:ℂ))^i • iteratedDeriv i f x
  let A' (i:ℕ):ℝ:=(d/r)^i * M
  have hr := g.trans p
  have H : 0 ≤ d/r := by positivity
  have B : d/r<1 := by rwa [div_lt_one hr]
  have hh := Complex.hasSum_taylorSeries_on_ball u.differentiableOn (closedBall_subset_ball p h)
  have hz(i:ℕ):‖F i‖ ≤ A' i := by
    have hp := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hr u v
    simp only [F,norm_smul,norm_inv,RCLike.norm_natCast,norm_pow] -- tune
    refine le_trans (b:=(i.factorial:ℝ)⁻¹*(d^i*((i.factorial:ℝ)*M/r^i))) ?_ (le_of_eq ?_)
    · gcongr
      exact mem_closedBall_iff_norm.mp h
    unfold A'; rw [div_pow]; field_simp
  change ‖f z- ∑ i ∈ Finset.range (n+1),F i‖ ≤ _
  have he:(∑' i, F (i+(n+1)))= f z - ∑ i ∈ Finset.range (n+1), F i := by
    rw [eq_sub_iff_add_eq]; exact (add_comm ..).trans ((hh.summable.sum_add_tsum_nat_add _).trans hh.tsum_eq) -- check sub'+ addition
  have h0: HasSum (fun i=> A' (i+(n+1))) ((d/r)^(n+1) * (1-d/r)⁻¹*M) := by
    simp_rw [A',pow_add]; refine ?_
    have ha:= hasSum_geometric_of_lt_one H B; convert (ha.mul_right ((d/r)^(n+1))).mul_right M using 1 <;> first | rfl | (funext i; rw [pow_add]) | ring
  rw [←he, ← h0.tsum_eq]
  have ht : Summable fun i:ℕ=> ‖F (i+(n+1))‖ := Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i => hz _) h0.summable
  exact (norm_tsum_le_tsum_norm ht).trans (Summable.tsum_le_tsum (fun i=> hz _) ht h0.summable)

omit e in
lemma approximate (n : ℕ) (z : ℂ) (h : z∈closedBall (x:ℂ) d) :
    ‖f z-(poly x d n f).eval z‖ ≤
      (1+64^(n+1)) *((d/r)^(n+1)*(1-d/r)⁻¹*M) := by
  let P:= nearT x f n
  let ω:= fun f : ℂ→ℂ => (poly x d n f).eval z
  let C:=((d/r)^(n+1)*(1-d/r)⁻¹*M)
  let l(i:ℕ) := weights x d n i z
  have t : ‖f z-P.eval z‖≤ C := taylor_price d g p u v n z h -- args tuner
  have hx : ω P.eval - ω f = ∑ i∈ Finset.range (n+1), l i*(P.eval (nodes x d n i)-f (nodes x d n i)) := by
    unfold ω; rw [poly_eval,poly_eval]; simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]
  have v' := cost_sum x (d:=d) g n h
  have v₀ : 0 ≤ C := (norm_nonneg _).trans t
  have hg : ‖ω P.eval - ω f‖ ≤ C * 64^(n+1) := by
    rw [hx,mul_comm]; refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g:=fun i=> ‖l i‖ * C) (fun i h=>?_)).trans ?_
    · rw [norm_mul,norm_sub_rev]; exact mul_le_mul_of_nonneg_left (taylor_price d g p u v n (nodes x d n i) (complex_inner x n g h)) (norm_nonneg _)
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right v' v₀
  rw [show ω P.eval=P.eval z from congrArg (Polynomial.eval z) (ifPol x d n g P (near_degree x f n))] at hg
  change ‖f z - ω f‖ ≤ _* C
  exact (norm_sub_le_norm_sub_add_norm_sub (f z) (P.eval z) _).trans ( (add_le_add t hg).trans (le_of_eq (by ring)))

end approx
end Sample
end YM.PolyDisc.Revival
