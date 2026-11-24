import YM.CF.Drapes.Epoch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes.Crown
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Branch Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {Q0 : License D} {a d K C : ℝ}
variable {A:Raw D I} {c r : ℝ}
lemma deck (N : ℕ) (E : 0<N) (h : Crown Q0 s s a c A) (p : Crown Q0 s s a r (fun x=> A x^N)) (ha : 0≤a) (hr : 0≤r)
    (H : 1≤ K) (H' : 2*c ≤ K) (n : ℕ) : Crown Q0 s s a (2 * (Real.exp a*(2*r)^(n/N) * (Real.exp a*K^N))) (fun x=>A x^n) := by
  have hm := h.powers ha (n%N); have hp : Crown Q0 s s a (Real.exp a*K^N) (fun x=>A x^(n%N)) := by
    apply hm.books
    obtain ⟨F,C,p,L,t⟩ := h
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (pow_le_pow_left₀ (mul_nonneg (by norm_num) L.posP) H' _).trans (pow_le_pow_right₀ H (Nat.le_of_lt (Nat.mod_lt _ E)))
  have ht (x:D) : A x^n=(A x^N)^(n/N)*A x^(n%N) := by rw [←pow_mul,←pow_add,Nat.div_add_mod]
  simp_rw [ht]
  exact (p.powers ha _).product hp ha
lemma craft {N : ℕ} (h : 0<N) (P : Crown Q0 s s a K A) (E : Crown Q0 s s d (1/4) (fun x=>A x^N)) (q : d≤a) (hd : 0<d) {k : ℝ} (hk : 0<k)
    (g : ∀ n, (1/2:ℝ)^(n/N)≤(k^N)⁻¹*k^n) (n : ℕ) :
    Crown Q0 s s d ((2 * (Real.exp d * (k^N)⁻¹ * (Real.exp d*(max 1 (2*K))^N))) * k^n) (fun x=>A x^n) := by
  apply ((P.drop q).deck N h E hd.le (by norm_num) (le_max_left ..) (le_max_right ..) n).books
  norm_num1
  have ht : 0 < Real.exp d := Real.exp_pos _
  calc
    _ ≤ 2 * (Real.exp d * ((k^N)⁻¹*k^n) * (Real.exp d*(max 1 (2*K))^N)) := by
      norm_num1 at * -- tune
      gcongr <;> first | exact g n | positivity
    _ = _ := by ring

end YM.CF.Drapes.Crown
