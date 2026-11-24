import YM.CF.Support.Power

/-! Post-grouping exponential fees; reusable by gapped inverses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter NormedSpace
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {A : Raw D I} {q r a c d K M u : ℝ}
lemma RootedK.deck (N : ℕ) (E : 0<N) (h : RootedK s s a c A) (p : RootedK s s a r (fun x=> A x^N)) (ha : 0≤a) (hr : 0≤r)
    (H : 1≤ K) (H' : 2*c ≤ K) (n : ℕ) : RootedK s s a (2 * (Real.exp a*(2*r)^(n/N) * (Real.exp a*K^N))) (fun x=>A x^n) := by
  have hm := h.powers ha (n%N); have hp : RootedK s s a (Real.exp a*K^N) (fun x=>A x^(n%N)) := by
    apply hm.books
    obtain ⟨F,C,p,L,t⟩ := h
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (pow_le_pow_left₀ (mul_nonneg (by norm_num) L.posP) H' _).trans (pow_le_pow_right₀ H (Nat.le_of_lt (Nat.mod_lt _ E)))
  have ht (x:D) : A x^n=(A x^N)^(n/N)*A x^(n%N) := by rw [←pow_mul,←pow_add,Nat.div_add_mod]
  simp_rw [ht]
  exact (p.powers ha _).product hp ha
-- bound div N by chosen exponential
lemma drift_name {N : ℕ} (h : 0<N) {q : ℝ} (e : 0<q) (p : q<1) : ∃ c:ℝ, 0<c ∧ c<1 ∧ ∀ n:ℕ, q^(n/N)≤(c^N)⁻¹*c^n := by
  let C := Real.exp (Real.log q/N); have ht : 0<C := Real.exp_pos _
  have hh : 0<(N:ℝ) := by exact_mod_cast h
  have hb : C<1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (Real.log_neg e p) hh)
  have hg : C^N=q := by unfold C; rw [←Real.exp_nat_mul, show (N:ℝ)*(Real.log q/N)=Real.log q by field_simp, Real.exp_log e]
  refine ⟨C,ht,hb,fun i=>?_⟩
  rw [mul_comm (C^N)⁻¹,←div_eq_mul_inv,le_div_iff₀ (pow_pos ht _), ← hg, ←pow_mul, ←pow_add]; apply pow_le_pow_of_le_one ht.le hb.le
  have he := Nat.div_add_mod i N; have hl := Nat.mod_lt i h; omega
/-- Cost at reduced geometric rate. -/
lemma tariff {N : ℕ} (h : 0<N) (P : RootedK s s a K A) (E : RootedK s s d (1/4) (fun x=>A x^N)) (q : d≤a) (hd : 0<d) {k : ℝ} (hk : 0<k)
    (g : ∀ n, (1/2:ℝ)^(n/N)≤(k^N)⁻¹*k^n) (n : ℕ) :
    RootedK s s d ((2 * (Real.exp d * (k^N)⁻¹ * (Real.exp d*(max 1 (2*K))^N))) * k^n) (fun x=>A x^n) := by
  apply ((P.drop q).deck N h E hd.le (by norm_num) (le_max_left ..) (le_max_right ..) n).books
  norm_num1
  have ht : 0 < Real.exp d := Real.exp_pos _
  calc
    _ ≤ 2 * (Real.exp d * ((k^N)⁻¹*k^n) * (Real.exp d*(max 1 (2*K))^N)) := by
      norm_num1 at * -- tune
      gcongr <;> first | exact g n | positivity
    _ = _ := by ring
lemma power_card [Nonempty I] {C u : ℝ} -- uniform choices, even when specializing d later
    (pC : 0≤C) (p : 0 < a) (pK : 0<K) (pu : 0<u) (pq : u<1) (g : 0 < c) :
    ∃ (N:ℕ) (d:ℝ), 0<N ∧ 0<d ∧ d≤a ∧ ∀ (b : Stage Y I D G) (s : Tag b) (F : Raw D I), GroupCost C a K u c N d b s F := by
  obtain ⟨P,p₀,p₁⟩ := exists_between pq
  obtain ⟨n,e,v,d,r,q,w,V⟩ := grouping pC p pK p₀ (pu.trans p₀) p₁ g
  exact ⟨n,d,e,r,q.trans (half_le_self p.le),fun b s F=>power_low C a K P c u n v d pC p.le (pu.trans p₀).le r.le q w V⟩
lemma rate_generic [Nonempty I] {C u : ℝ} (pC : 0≤C) (p : 0<a) (pk : 0<K) (pu : 0<u) (q : u<1) :
    ∃ a' k m : ℝ, 0<a' ∧ a'≤a ∧ 0<k ∧ k<1 ∧ 0<m ∧ ∀ (b : Stage Y I D G) (s : Tag b) (F : Raw D I), Capacity b C→RootedK s s a K F→(∀ x, ‖F x‖≤u)→ ∀ n:ℕ, RootedK s s a' (m*k^n) (fun x => F x^n) := by
  obtain ⟨N,d,h,H,l,Q⟩ := power_card (Y:=Y) (I:=I) (D:=D) (G:=G) pC p pk pu q (show 0<(1:ℝ)/4 by norm_num)
  obtain ⟨k,hk,w,g⟩ := drift_name h (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
  exact ⟨d,k,_,H,l,hk,w,by positivity,fun b s f Hb Hp g' n=>tariff h Hp (Q b s f Hb Hp g') l H hk g n⟩ -- choose via spread across types later

-- inverse eval via series
lemma route_inv {A : Op I} (g : ‖A‖<1) : ∑' k:ℕ,A^k=(1-A)⁻¹ := by
  have ht : (1-A)*(∑' k:ℕ,A^k)=1 := (summable_geometric_of_norm_lt_one g).one_sub_mul_tsum_pow
  have hp := live (live_of ht)
  calc _ = (1-A)⁻¹ * ((1-A)*(∑' k:ℕ,A^k)) := by rw [←mul_assoc,hp.2,one_mul]
       _ = _ := by rw [ht,mul_one]
lemma RootedK.wind (p : 0≤a) {m : ℝ} (h : RootedK s s a m A) (hm : 0≤m) :
    RootedK s s a (∑' n:ℕ, ‖((n.factorial:ℂ)⁻¹)‖ * (Real.exp a * (2*m)^n)) (fun x:D=> exp (A x)) := by
  rw [exp_eq_tsum ℂ]
  have he := ((norm_expSeries_summable' (𝕂:=ℂ) ((2*m:ℝ):ℂ)).mul_left (Real.exp a)) -- tune
  have hS : Summable (fun n:ℕ=> ‖(n.factorial:ℂ)⁻¹‖*(Real.exp a * (2*m)^n)) := by
    apply he.congr; intro i
    rw [norm_smul,norm_pow, Complex.norm_real,Real.norm_of_nonneg (by positivity)]; ring
  exact RootedK.tsK _ (fun n=>(h.powers p n).raise _) p hS
end YM.CF.Branch
