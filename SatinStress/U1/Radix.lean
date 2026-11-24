import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Exact polynomial tests, part 1

Use Kronecker substitution in every rank check: once to prove pivots (no degree
checks needed there) and also for the upper bound, but then checking the degree
is absolutely essential. Work over ℂ throughout the polynomial argument; rows
will test ℝ-spans as well. No result conditional on generic numerical sampling or
on reducing mod primes.
-/
namespace SatinStress.U1
namespace Radix

open Finset MvPolynomial
open scoped BigOperators Polynomial

def base : ℕ := 64
def wt {n : ℕ} (i : Fin n) : ℕ := base ^ i.val

def digits {n : ℕ} (s : Fin n → ℕ) := ∑ i, wt i * s i
lemma digits_succ {n : ℕ} (s : Fin (n+1) → ℕ) :
    digits s = s 0 + base * digits (fun i : Fin n => s i.succ) := by
  unfold digits
  rw [Fin.sum_univ_succ,mul_sum]
  congr 1
  · simp [wt]
  apply sum_congr rfl; intro i hi; simp [wt,pow_succ']; rw [mul_assoc]

lemma identifies {n : ℕ} {s t : Fin n → ℕ} (h : ∀ i, s i < base) (ht : ∀ i, t i < base) (e : digits s = digits t) :
    s = t := by
  induction n with
  | zero => exact Subsingleton.elim ..
  | succ n ih =>
    rw [digits_succ, digits_succ] at e
    have h0 := h 0; have h1 := ht 0
    have hh : s 0 = t 0 := by unfold base at h0 h1 e; omega
    have he := ih (s:=fun i => s i.succ) (t:=fun i => t i.succ) (fun i => h _) (fun i => ht _) (by unfold base at e; omega)
    exact funext fun i => Fin.cases (motive:=fun i => s i = t i) hh (fun i => congr_fun he i) i

abbrev Many := MvPolynomial (Fin 9) ℂ

noncomputable def encode : Many →ₐ[ℂ] ℂ[X] :=
  aeval fun i : Fin 9 => Polynomial.X ^ wt i

@[simp]
lemma encode_X (i : Fin 9) : encode (X i) = Polynomial.X ^ wt i := by simp [encode]
@[simp]
lemma encode_C (c : ℂ) : encode (C c) = Polynomial.C c := by simp [encode]

lemma encode_monomial (s : Fin 9 →₀ ℕ) (x : ℂ) :
    encode (monomial s x) = Polynomial.monomial (digits s) x := by
  rw [encode, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Polynomial.C_mul_X_pow_eq_monomial]
  change Polynomial.C x * (∏ i : Fin 9, (Polynomial.X ^ wt i) ^ s i) = _
  simp_rw [← pow_mul]; rw [prod_pow_eq_pow_sum]; rfl

lemma encode_detect {p : Many} (h : p.totalDegree < base) (e : encode p = 0) : p = 0 := by
  have ht (i) s (hs : s ∈ p.support) : (s : Fin 9 →₀ ℕ) i < base :=
    ((monomial_le_degreeOf _ hs).trans (degreeOf_le_totalDegree p i)).trans_lt h
  classical
  by_contra y
  obtain ⟨s,hs⟩ := support_nonempty.mpr y
  have he := congr_arg (fun f => Polynomial.coeff (R:=ℂ) f (digits s)) e
  rw [p.as_sum,map_sum] at he
  change (∑ i ∈ _, encode (monomial i (_ : ℂ))).coeff _ = (0 : ℂ) at he -- coeff_zero defeq?
  simp_rw [Polynomial.finsetSum_coeff, encode_monomial] at he
  rw [sum_eq_single_of_mem s hs] at he
  · rw [Polynomial.coeff_monomial] at he; exact (mem_support_iff.mp hs) (by simpa using he)
  intro t hm hy
  apply Polynomial.coeff_monomial_of_ne
  exact fun E => hy (DFunLike.coe_injective (identifies (fun i => ht i t hm) (fun i => ht i s hs) E.symm))

-- rows for both ℂ and ℝ spans
noncomputable def test (r : ℕ) : Many →ₗ[ℂ] ℂ :=
  (Polynomial.lcoeff ℂ r).comp encode.toLinearMap
@[simp] lemma test_at (r : ℕ) (p : Many) : test r p = (encode p).coeff r := rfl
end Radix
end SatinStress.U1
