import YM.CF.Support.Hit

/-! Quadratic-error transfer comparison, only fixed-volume convergence here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF
open scoped Topology
open Filter Finset NormedSpace
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

def restP (a : A) (x : ℝ) := exp (x • a)-1-x • a
lemma rest_near (a : A) : ∃ c ≥ (0:ℝ),∀ t ∈ Set.Icc (0:ℝ) 1, ‖restP a t‖≤t^2*c := by
  let F (t : ℝ) (i : ℕ) : A := ((i.factorial:ℝ)⁻¹) • ((t • a)^i)
  have he (t : ℝ) : Summable (F t) := by exact expSeries_summable' _ -- tune
  have h : Summable (fun i:ℕ=> ‖F 1 (i+2)‖) := by exact (summable_nat_add_iff 2).mpr (show Summable (fun i=>‖F 1 i‖) from norm_expSeries_summable' (𝕂:=ℝ) ((1:ℝ) • a))
  refine ⟨∑' i:ℕ, ‖F 1 (i+2)‖,tsum_nonneg (fun _=>norm_nonneg _),?_⟩
  intro t ht; have hp := ht.1; have hc := ht.2
  have H : Summable (fun i=>F t (i+2)) := (summable_nat_add_iff 2).mpr (he t)
  have hx (i:ℕ) : ‖F t (i+2)‖≤t^2*‖F 1 (i+2)‖ := by
    have hh : F t (i+2)=t^(i+2) • F 1 (i+2) := by unfold F; rw [smul_pow,one_smul,smul_comm]
    rw [hh,norm_smul,Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [add_comm i, pow_add]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hp hc)
  have ht : restP a t=∑' i:ℕ,F t (i+2) := by
    unfold restP; rw [exp_eq_tsum ℝ]; change (∑' i:ℕ,F t i)-1-t • a=_
    rw [← (he t).sum_add_tsum_nat_add 2]; norm_num [Finset.sum_range_succ,F]; abel -- tune
  rw [ht]; apply (norm_tsum_le_tsum_norm ((h.mul_left (t^2)).of_nonneg_of_le (fun _=>norm_nonneg _) hx)).trans
  exact (((h.mul_left _).of_nonneg_of_le (fun _=>norm_nonneg _) hx).tsum_le_tsum hx (h.mul_left _)).trans (le_of_eq (h.tsum_mul_left _))

lemma power_le_press {N Q : A} (n : ℕ) (r s : ℝ) (q : 0≤r) (p : ‖N‖ ≤ r) (v : ‖Q‖≤r) (h : ‖N-Q‖≤s) : ‖N^(n+1)-Q^(n+1)‖≤(n+1:ℝ)*r^n*s := by
  induction n with
  | zero=> simpa
  | succ n ih=>
    rw [pow_succ N (n+1),pow_succ Q (n+1),show N^(n+1)*N-Q^(n+1)*Q=N^(n+1)*(N-Q)+(N^(n+1)-Q^(n+1))*Q by rw [mul_sub,sub_mul]; abel]
    apply (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) p _)) h (norm_nonneg _) (by positivity))) ((norm_mul_le ..).trans (mul_le_mul ih v (norm_nonneg _) ((norm_nonneg _).trans ih)))).trans ?_)
    simp only [pow_succ]; push_cast; exact le_of_eq (by ring)

def stampE (a b : A) (t : ℝ) := 1 + t • a + t^2 • b
local notation "λ₀" => fun (i : ℕ)=> (i+1:ℝ)⁻¹
lemma euler (a b : A) : Tendsto (fun i:ℕ=> stampE a b (λ₀ i)^(i+1)) atTop (𝓝 (exp a)) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨c,hc,H⟩ := rest_near a
  let C := ‖a‖+‖b‖+c; have hc' : 0≤C := by unfold C; positivity
  let f := λ₀
  have hp : ∀ i, f i ∈ Set.Icc (0:ℝ) 1 := fun i=> ⟨by unfold f; positivity,inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg i (α:=ℝ))])⟩
  let r := Real.exp C
  let X := fun i:ℕ=>stampE a b (f i)
  have hk (i : ℕ) : ‖X i ^ (i+1)-exp a‖ ≤ f i *(r*(‖b‖+c)) := by
    let t := f i; let R := Real.exp (C*t); let Q := exp (t • a)
    have he := H _ (hp i); have ht : 0≤t := (hp i).1; have hB : t≤1 := (hp i).2; have hz : t^2 ≤ t := by nlinarith
    have hj : Q=1+t • a+restP a t := by unfold Q restP; abel
    have hy : 1+C*t≤R := by simpa [add_comm] using Real.add_one_le_exp (C*t)
    have HW (p : A) (g:‖p‖≤t^2*(‖b‖+c)) : ‖(1:A)+t • a+p‖≤R := by
      calc
        _ ≤ _ := (norm_add_le ..).trans (add_le_add (norm_add_le ..) g)
        _ ≤ R := by rw [norm_smul,norm_one,Real.norm_of_nonneg ht]; apply le_trans _ hy; unfold C; nlinarith [mul_le_mul_of_nonneg_right hz (show 0≤‖b‖+c by positivity)]
    have hh : Q^(i+1)=exp a := by
      unfold Q; rw [←exp_nsmul]; apply congrArg exp
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,show (↑(i+1):ℝ)*t=1 by unfold t f; push_cast; field_simp,one_smul]
    have hX : ‖X i‖ ≤ R := HW (t^2 • b) (by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hc) (by positivity))
    have hv : ‖Q‖≤R := by rw [hj]; apply HW; exact he.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) (by positivity))
    have hx : ‖X i-Q‖ ≤ t^2*(‖b‖+c) := by
      rw [hj]; change ‖(1+t • a+ t^2 • b)-(1+t • a+restP a t)‖≤_; rw [add_sub_add_left_eq_sub, mul_add]; apply (norm_sub_le ..).trans; rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact add_le_add le_rfl he
    rw [←hh]; apply (power_le_press i R _ (Real.exp_pos _).le hX hv hx).trans
    have hi : 1 ≤ R := Real.one_le_exp (mul_nonneg hc' ht)
    have hu : (i+1:ℝ)*t=1 := by unfold t f; field_simp
    have hV : R^(i+1)=r := by unfold R r; rw [←Real.exp_nat_mul]; apply congrArg Real.exp; push_cast; rw [mul_left_comm,hu,mul_one]
    calc
      _ ≤ (i+1:ℝ)*r*(t^2*(‖b‖+c)) := by rw [←hV]; gcongr; omega
      _ = _ := by change _=t * _; calc _ = ((i+1:ℝ)*t)*(t*(r*(‖b‖+c))) := by ring
                                        _ = _ := by rw [hu,one_mul]
  rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero (fun _=>norm_nonneg _) hk
  have hp : Tendsto f atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simpa only [zero_mul] using hp.mul_const (r*(‖b‖+c))
end YM.CF
