import YM.Spectral.Projection
-- Only helper analysis here. M4 instantiation will use SU5SatinFixedProbesAndBareFlavorNovember6

/-!
# Smooth vectors for an energy grading

This is used with **unit energy bands, including zero**, of `Spine.seasons`
(separately elected continuous spatial-translation Hilbert system, axis 3).
We use weighted *l¹* estimates of Hilbert norms. In particular the topology
of radial convergence in these estimates shouldn't be mistaken for convergence
in the inherited Hilbert norm alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace
variable {H : Hilbert}

/-- Only the energy grading, not assuming anything analogous for the local
sector projections. -/
structure Grading (H : Hilbert) where
  P (n : ℕ) : H.Op
  real (n : ℕ) : (P n).adjoint = P n
  same (n : ℕ) : (P n).comp (P n) = P n
  other {m n : ℕ} : m ≠ n → (P m).comp (P n) = 0
  sum (x : H) : HasSum (fun n => P n x) x

namespace Grading

variable (G : Grading H)

-- use real weights throughout
abbrev weight (k n : ℕ) : ℝ := ((n+1:ℕ):ℝ) ^ k
lemma one_le_weight (k n : ℕ) : 1 ≤ weight k n :=
  one_le_pow₀ (by exact_mod_cast (Nat.le_add_left 1 n))
lemma weight_pos (k n : ℕ) : 0 < weight k n :=
  zero_lt_one.trans_le (one_le_weight k n)
lemma weight_mono (n : ℕ) {i j : ℕ} (h : i ≤ j) : weight i n ≤ weight j n :=
  pow_le_pow_right₀ (by exact_mod_cast (Nat.le_add_left 1 n)) h

/-- The amount of the `k`-th domain norm spent on band `n`. -/
def due (x : H) (k n : ℕ) : ℝ := weight k n * ‖G.P n x‖
lemma due_nonneg (x : H) (k n : ℕ) : 0 ≤ G.due x k n :=
  mul_nonneg (weight_pos k n).le (norm_nonneg _)
lemma due_add (x y : H) (k n : ℕ) : G.due (x+y) k n ≤ G.due x k n + G.due y k n := by
  unfold due; rw [map_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le ..) (weight_pos k n).le
lemma due_smul (x : H) (k n : ℕ) (c : ℂ) : G.due (c • x) k n = ‖c‖ * G.due x k n := by
  unfold due; rw [map_smul, norm_smul, mul_left_comm]
lemma due_mono (x : H) (n : ℕ) {i j : ℕ} (h : i ≤ j) : G.due x i n ≤ G.due x j n :=
  mul_le_mul_of_nonneg_right (weight_mono _ h) (norm_nonneg _)

/-- Common test domain. -/
def domain : Submodule ℂ H where
  carrier := {x|∀ k, Summable (G.due x k)}
  zero_mem' k := by
    change Summable (fun n => G.due 0 k n); simpa only [due,map_zero,norm_zero,mul_zero] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
  add_mem' := fun {x y} (hx : ∀ k, _) (hy : ∀ k, _) k =>
    ((hx k).add (hy k)).of_nonneg_of_le (G.due_nonneg _ k) (G.due_add x y k)
  smul_mem' c x (hx : ∀ k, _) k := by
    change Summable (fun n => G.due (c • x) k n); simp_rw [G.due_smul]; exact (hx k).mul_left _

variable {G}
lemma rapid {x : H} (hx : x ∈ G.domain) (k : ℕ) : Summable (G.due x k) := hx k

variable (G)
/-- Use only with `domain` membership. -/
def budget (k : ℕ) (x : H) : ℝ := ∑' n, G.due x k n
lemma budget_nonneg (k : ℕ) (x : H) : 0 ≤ G.budget k x := tsum_nonneg (G.due_nonneg x k)
lemma budget_add (k : ℕ) {x y : H} (hx : x ∈ G.domain) (hy : y ∈ G.domain) :
    G.budget k (x+y) ≤ G.budget k x + G.budget k y := by
  unfold budget; rw [←(rapid hx k).tsum_add (rapid hy k)]
  exact (rapid (G.domain.add_mem hx hy) k).tsum_le_tsum (G.due_add x y k) ((rapid hx k).add (rapid hy k))
lemma budget_smul (k : ℕ) (x : H) (c : ℂ) : G.budget k (c • x) = ‖c‖ * G.budget k x := by
  unfold budget; simp_rw [G.due_smul]; rw [tsum_mul_left]
lemma budget_mono {i j : ℕ} (h : i ≤ j) {x : H} (hx : x ∈ G.domain) :
    G.budget i x ≤ G.budget j x :=
  (rapid hx i).tsum_le_tsum (fun n => G.due_mono x n h) (rapid hx j)
lemma budget_zero {x : H} (hx : x ∈ G.domain) : ‖x‖ ≤ G.budget 0 x := by
  simp only [budget, due, weight, pow_zero, one_mul];
  nth_rw 1 [← (G.sum x).tsum_eq]; exact norm_tsum_le_tsum_norm (by simpa only [due, weight, pow_zero, one_mul] using (show Summable (fun n => G.due x 0 n) from rapid hx 0))

lemma project_same (x : H) (n : ℕ) : G.P n (G.P n x) = G.P n x := DFunLike.congr_fun (G.same n) x
lemma project_other (x : H) {m n : ℕ} (h : m ≠ n) : G.P m (G.P n x) = 0 := DFunLike.congr_fun (G.other h) x
lemma project_orth (x y : H) (n : ℕ) : inner ℂ x (G.P n y) = inner ℂ (G.P n x) y := by
  nth_rw 2 [← G.real n]; exact (ContinuousLinearMap.adjoint_inner_left ..).symm
lemma project_mem (x : H) (n : ℕ) : G.P n x ∈ G.domain := by
  intro k
  exact summable_of_ne_finset_zero (s:={n}) (fun j h=> by rw [due,G.project_other x (by simpa using h),norm_zero,mul_zero])
lemma budget_project (x : H) (n k : ℕ) : G.budget k (G.P n x) = G.due x k n := by
  unfold budget
  rw [tsum_eq_single n]; · unfold due; rw [G.project_same]
  intro j h; rw [due,G.project_other x h,norm_zero,mul_zero]
lemma project_le (x : H) (n : ℕ) : ‖G.P n x‖ ≤ ‖x‖ := by
  by_cases h : G.P n x = 0
  · rw [h,norm_zero]; exact norm_nonneg x
  have ht : inner ℂ x (G.P n x) = inner ℂ (G.P n x) (G.P n x) := by
    conv_lhs => rhs; rw [← G.project_same x n]
    rw [G.project_orth]
  have hv := norm_inner_le_norm x (G.P n x) (𝕜:=ℂ)
  rw [ht, inner_self_eq_norm_sq_to_K] at hv; simp only [norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hv
  exact le_of_mul_le_mul_right (by rw [← pow_two]; exact hv) (norm_pos_iff.mpr h)
lemma norm_project_le (n : ℕ) : ‖G.P n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa only [one_mul] using G.project_le x n)
lemma grade_dense : Dense (G.domain : Set H) := fun x =>
  mem_closure_of_tendsto (G.sum x) (Eventually.of_forall fun _ => G.domain.sum_mem (fun i _ => G.project_mem x i))

/-- Convergence in all the domain norms, for domain-vector families. This is
not `Tendsto` in the inherited norm topology. -/
def Approaches {ι : Type*} (f : Filter ι) (X : ι → G.domain) (x : G.domain) : Prop :=
  ∀ k, Tendsto (fun i => G.budget k ((X i).1 - x.1)) f (𝓝 0)

lemma Approaches.hilbert {ι : Type*} {f : Filter ι} {X : ι → G.domain} {x : G.domain}
    (h : G.Approaches f X x) : Tendsto (fun i => (X i).1) f (𝓝 x.1) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _=> norm_nonneg _)
    (fun i=> G.budget_zero (G.domain.sub_mem (X i).2 x.2)) (h 0))

lemma budget_project_patch (x : H) (k n : ℕ) (J : Finset ℕ) :
    G.due (x-∑ i ∈ J, G.P i x) k n =
      if n ∈ J then 0 else G.due x k n := by
  unfold due; rw [map_sub, map_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem n h, G.project_same, sub_self,norm_zero,mul_zero]
    exact fun i _ p=> G.project_other x p.symm
  · rw [Finset.sum_eq_zero, sub_zero]; exact fun i p=> G.project_other x (by aesop)

/-- Finite spectral patch projection, for use on the domain. -/
def patch (x : G.domain) (J : Finset ℕ) : G.domain :=
  ⟨∑ i ∈ J, G.P i x.1, G.domain.sum_mem fun i _=> G.project_mem x.1 i⟩
lemma due_neg (x : H) (k n : ℕ) : G.due (-x) k n = G.due x k n := by rw [due,map_neg,norm_neg,due]
lemma budget_neg (x : H) (k : ℕ) : G.budget k (-x) = G.budget k x := by simp only [budget,due_neg]
lemma budget_patch (x : G.domain) (k : ℕ) (J : Finset ℕ) :
    G.budget k ((G.patch x J).1-x.1) = G.budget k x.1-∑ i ∈ J, G.due x.1 k i := by
  have hu : G.budget k ((G.patch x J).1-x.1) = G.budget k (x.1-(G.patch x J).1) := by
    rw [← G.budget_neg (x.1-_) k, neg_sub]
  rw [hu]; simp only [budget]; change (∑' n, G.due (x.1-∑ i∈J,G.P i x.1) k n)=_
  let paid (n : ℕ) := if n∈J then G.due x.1 k n else 0
  simp_rw [G.budget_project_patch, show ∀ n, (if n∈J then 0 else G.due x.1 k n)=G.due x.1 k n-paid n from fun n=> by by_cases e:n∈J <;> simp [e,paid]]
  rw [(rapid x.2 k).tsum_sub (summable_of_ne_finset_zero (s:=J) (fun n h=> by simp [paid,h])),tsum_eq_sum (s:=J) (f:=paid) (fun n h=>by simp [paid,h])]
  rw [Finset.sum_congr rfl (show ∀ n∈J, paid n=G.due x.1 k n from fun n h=>if_pos h)]

lemma approaches_patch (x : G.domain) : G.Approaches atTop (G.patch x) x := by
  intro k; simp_rw [G.budget_patch]
  rw [show (0:ℝ)=G.budget k x.1-G.budget k x.1 from (sub_self _).symm]
  exact tendsto_const_nhds.sub (show Tendsto _ _ _ from (rapid x.2 k).hasSum)

/-- Useful product-limit estimate, priced in domain budgets. -/
lemma approaches_apply {ι : Type*} {f : Filter ι}
    (A : ι → (G.domain →ₗ[ℂ] G.domain)) (B : G.domain →ₗ[ℂ] G.domain)
    (h : ∀ k, ∃ (l : ℕ) (C : ℝ), ∀ᶠ i in f, ∀ z : G.domain, G.budget k (A i z).1 ≤ C*G.budget l z.1)
    (u : ∀ z, G.Approaches f (fun i => A i z) (B z))
    {X : ι → G.domain} {x : G.domain} (t : G.Approaches f X x) :
    G.Approaches f (fun i => A i (X i)) (B x) := by
  intro k; let z:=B x
  obtain ⟨l,C,hc⟩:= h k
  change Tendsto (fun i => G.budget k ((A i (X i)).1-z.1)) f (𝓝 0)
  have ht:=((t l).const_mul C).add (u x k); rw [mul_zero,add_zero] at ht
  refine squeeze_zero' (Eventually.of_forall fun i=>G.budget_nonneg k _) ?_ ht
  filter_upwards [hc] with i p
  let y := A i (X i-x); let v := A i x-z
  change G.budget k _ ≤ _+_
  calc G.budget k _ = G.budget k (y.1+v.1) := by unfold y v z; rw [map_sub]; congr 1; push_cast; abel
       _ ≤ G.budget k y.1 + G.budget k v.1 := G.budget_add _ y.2 v.2
       _ ≤ C*G.budget l ((X i).1 - x.1)+ G.budget k v.1 := add_le_add (p (X i-x)) le_rfl
end Grading
end YM.SatinRegistration
