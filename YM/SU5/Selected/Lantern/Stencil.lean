import YM.SU5.Selected.Lantern.Blend
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
/-!
# Phase-count selector. Identity plus ONLY odd & 1-mod-five monomials.
One λ cancellation per degree, **number of marks not positions in spacetime**.
Coefficients exponential not factorial. Later applied to normalized path moments.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern.Stencil
open Function Finset Polynomial BigOperators
variable (r n :ℕ)(p:n<r)
def load(n:ℕ):ℕ:=10*n+1
def coord(n:ℕ):ℝ:= load n
def bill (i:ℕ):ℝ:= if i<r then (Lagrange.basis (range r) coord i).eval 0 else 0
lemma submit(p:ℝ[X])(h: p.natDegree<r) : ∑ i∈range r,p.eval (coord i)*bill r i=p.eval 0 := by
 have ht:Injective coord:= Nat.cast_injective.comp (show Injective load from (by intro x y h; unfold load at h; omega))
 have h₀:p.degree < (range r).card:=by rw [card_range]; exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast h)
 have he:(Lagrange.interpolate (range r) coord (fun i=>p.eval (coord i)))= p:= (Lagrange.eq_interpolate ht.injOn h₀).symm
 calc _ = eval (0:ℝ) (Lagrange.interpolate (range r) coord (fun i=>p.eval (coord i))) := by rw [Lagrange.interpolate_apply,Polynomial.eval_finsetSum]; apply sum_congr rfl; intro i p'; rw [bill,if_pos (mem_range.mp p'),eval_mul,eval_C]
      _ = _ := by rw [he]
include p
lemma cheers : (∑ i∈range r,((load i).choose n:ℝ)*bill r i )= if n=0 then (1:ℝ) else 0:=by
 let Q:= descPochhammer ℝ n; have e:= submit r Q (by unfold Q; rwa [descPochhammer_natDegree]); simp_rw [Nat.cast_choose_eq_descPochhammer_div ℝ,div_mul_eq_mul_div,←sum_div]; rw [show (∑ i∈_,eval ((load i:ℕ):ℝ) Q* _)= Q.eval 0 from e] -- tune synt
 by_cases k:n=0<;> simp [k,Q,descPochhammer_eval_zero] -- check
omit p
private def facbill(n:ℕ):ℝ:= Nat.factorial n
lemma facbill_pos (n:ℕ): 0<facbill n:=Nat.cast_pos.mpr (Nat.factorial_pos n)
private lemma fares {a b:ℕ}(h:a≠b): |eval (0:ℝ) (Lagrange.basisDivisor (coord b) (coord a))| ≤ (a+1:ℝ) / |(b:ℝ)-(a:ℝ)| :=by
 unfold Lagrange.basisDivisor; rw [eval_mul,eval_sub,eval_X,eval_C,eval_C,abs_mul,abs_inv]; unfold coord load; push_cast; rw [show (10*(b:ℝ)+1)-(10*(a:ℝ)+1)=10*(b-a) by ring, abs_mul, abs_of_pos (show (0:ℝ)<10 by norm_num), mul_inv]; have ht: (b:ℝ) ≠ a:= by exact_mod_cast h.symm
 field_simp -- positive denominators?
 rw [zero_sub,abs_neg,abs_of_nonneg (by positivity)]; linarith
private lemma back {i:ℕ}: (∏ k∈range i,|(i:ℝ)-k|)= facbill i:=by
 let f(k:ℕ):= (i:ℝ)-k
 calc (∏ k∈range i, _)= ∏ k∈range i, f k:=by apply prod_congr rfl; intro k g; rw [abs_of_pos (show 0<f k from sub_pos.mpr (by exact_mod_cast mem_range.mp g))]
      _ = ∏ k∈range i, ((k+1:ℕ):ℝ) := by
          rw [←Finset.prod_range_reflect (f:=f)] -- inspect; maybe exact
          apply prod_congr rfl; intro k g; unfold f; simp only [mem_range] at g
          push_cast [show k ≤ i-1 by omega, show 1 ≤ i by omega]; ring
      _ = _:= by unfold facbill; rw [←Finset.prod_range_add_one_eq_factorial,Nat.cast_prod]
private lemma forward (i j:ℕ) : (∏ k∈ Ico (i+1) (i+1+j), |(i:ℝ)-k|)=facbill j:=by
 induction j with
 | zero=> simp [facbill]
 | succ j ih=> rw [←add_assoc (i+1),prod_Ico_succ_top,ih] -- tune
               have h: (i:ℝ)-( (i+1+j:ℕ):ℝ) ≤ 0:=by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) j]; -- scope
               rw [abs_of_nonpos h]; unfold facbill; rw [Nat.factorial_succ]; push_cast; ring
               omega
local notation "S"=> (range r).erase n
include p
private lemma gust : (∏ k∈(S),|(n:ℝ)-k|)= facbill n*facbill (r-1-n):=by
 let a:=range n; let t:=r-1-n; let b:=Ico (n+1) (n+1+t)
 rw [show (S)=a∪b from ?_,prod_union,back,forward n];
 · exact disjoint_left.mpr (fun x v g=>(by have ht:= mem_Ico.mp g|>.1; have he:=mem_range.mp v; omega))
 · ext i; simp [a,b,t]; omega
lemma budget : |bill r n| ≤ (2:ℝ)^r:=by
 unfold bill Lagrange.basis; rw [if_pos p,eval_prod,Finset.abs_prod];
 apply ((Finset.prod_le_prod (fun _ _=> abs_nonneg _) (fun i (e:i∈ S)=> fares (b:=n) (a:=i) (ne_of_mem_erase e)))).trans
 rw [prod_div_distrib, gust r n p]
 let N:= (r-1-n); have ht: ∀ i:ℕ,(i+1:ℝ)*facbill i=facbill (i+1):=fun i=>by unfold facbill; rw [Nat.factorial_succ]; push_cast; rfl
 have hv : (∏ i∈ S,(↑i+1:ℝ))*(↑n+1:ℝ)=facbill r:=by
    rw [Finset.prod_erase_mul _ _ (mem_range.mpr p),facbill,←prod_range_add_one_eq_factorial]; push_cast; rfl
 have hx:((r.choose (n+1):ℕ):ℝ)*facbill (n+1)*facbill N=facbill r:=by
    unfold facbill; norm_cast; rw [show N=r-(n+1) by unfold N; omega,Nat.choose_mul_factorial_mul_factorial p]
 have he: (n:ℝ)+1>0:=(by positivity); rw [←ht] at hx; have hp:=facbill_pos n; have hw:=facbill_pos N; apply le_trans _ (show ( (r.choose (n+1):ℕ):ℝ) ≤ 2^r by exact_mod_cast Nat.choose_le_two_pow r (n+1)); apply le_of_eq; refine (div_eq_iff (show facbill n*facbill N ≠ 0 by positivity)).mpr ?_; -- nlinarith or cancel *
 apply mul_right_cancel₀ he.ne'; rw [hv,←hx]; change _ = (_*(facbill n*facbill N))*_; ring
 -- fix sed
end YM.CF.Pannier.Chancel.Lantern.Stencil
