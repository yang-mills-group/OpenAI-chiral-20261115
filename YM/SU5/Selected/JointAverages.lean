import YM.SU5.Selected.Character -- for types and later application
/-! # Compute a ground projection for bounds in every phase simultaneously

Countable means. Don't require commute for this (though compatible mesh forms do have it).
Use von Neumann mean ergodic averaging about each finite-depth lazy propagation rule
(the rule uses only true contractions; no alternates stacked into a signed/nonconvex mean).
Then also vote a limit of these projections via Vacancy `falling`. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 230000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Companies
open Function Filter Set Analysis
open scoped Matrix MatrixOrder Topology InnerProductSpace ComplexOrder Classical

section abstract
variable {X : Type} [Semiring X] [Algebra ℂ X]

def blend (F : ℕ → X) : ℕ → X
| 0 => 1
| n+1 => (1/2:ℂ) • (blend F n + F n)
def mix (x : X) (n : ℕ) := (n:ℂ)⁻¹ • ∑ i∈Finset.range n,x^i
variable {Y : Type} [Semiring Y] [Algebra ℂ Y]

lemma blend_map (f : X→ₐ[ℂ] Y) (F : ℕ→X) (n : ℕ) : f (blend F n)=blend (f ∘ F) n := by induction n with| zero=> exact map_one f| succ n ih=> rw [blend,map_smul,map_add,ih]; rfl
lemma mix_map (f : X→ₐ[ℂ] Y) (x : X) (n : ℕ) : f (mix x n)=mix (f x) n:= by simp [mix]
end abstract
section Hilb
variable (H : Hilbert) (F : ℕ→H.Op)
local notation "Τ" n:max => blend F n
private lemma blend_apply (x : H) (n : ℕ) : (Τ (n+1)) x = (1/2:ℂ) • ((Τ n) x + F n x) := rfl
lemma blend_small (p : ∀ i,‖F i‖≤1) (n : ℕ) : ‖Τ n‖ ≤ 1 := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v; rw [one_mul]; exact le_rfl
  | succ n ih =>
    rw [blend,norm_smul, norm_div]; norm_num; nlinarith only [norm_add_le (Τ n) (F n),p n,ih]
private lemma individually (x y z : H) (p : (1/2:ℂ) • (x+y)=z) (k : ‖x‖ ≤ ‖z‖) (h : ‖y‖ ≤ ‖z‖) : x=z := by
  have u (x : H) (hx : ‖x‖ ≤ ‖z‖) : (inner ℂ x z).re ≤ ‖z‖^2:= by
     rw [sq]; exact (Complex.re_le_norm _).trans ((norm_inner_le_norm (𝕜:=ℂ) ..).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ) k
  change (inner ℂ x z).re= _
  have ht : (inner ℂ ((1/2:ℂ) • (x+y)) z).re = ‖z‖^2:= by rw [p]; exact inner_self_eq_norm_sq (𝕜:=ℂ) z
  rw [inner_smul_left,inner_add_left,Complex.mul_re,Complex.add_re] at ht
  norm_num at ht; linarith [u x k,u y h]

lemma fixed (p : ∀ i,‖F i‖≤1) (n : ℕ) (x : H) : (Τ n) x=x ↔ ∀ i<n,F i x=x := by
  induction n with
  | zero => exact ⟨fun _ i h => (Nat.not_lt_zero _ h).elim,fun _=>rfl⟩
  | succ n ih =>
    have h₁(T : H.Op)(h : ‖T‖≤1): ‖T x‖≤‖x‖ := (T.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) h)
    rw [blend_apply]; constructor
    · intro a i e; obtain rfl|H' := eq_or_ne i n
      · exact individually H _ _ _ ((add_comm (F i x) ((blend F i) x)) ▸ a) (h₁ _ (p i)) (h₁ _ (blend_small H F p i))
      exact ih.mp (individually H _ _ _ a (h₁ _ (blend_small H F p n)) (h₁ _ (p n))) _ (by omega)
    intro a; rw [ih.mpr (fun i z=> a i (by omega)), a n (by omega),← two_smul ℂ,smul_smul]; norm_num

abbrev fixedAt (n : ℕ) := (Τ n).eqLocus (1:H.Op)
abbrev stationary := ⨅ n:ℕ, fixedAt H F n
lemma standing (x : H) (h : ∀ i,‖F i‖≤1) : x∈ stationary H F ↔ ∀ i, F i x=x := by
  rw [stationary,Submodule.mem_iInf]; constructor
  · exact fun p n=> (fixed H F h (n+1) x).mp (p _) n (by omega)
  exact fun k i => (fixed H F h i x).mpr (fun i _=> k i)
lemma descending (h : ∀ i,‖F i‖≤1) : Antitone (fixedAt H F) := fun i j p x a =>
  (fixed H F h i x).mpr (fun n q=> (fixed H F h j x).mp a _ (lt_of_lt_of_le q p))
lemma closedFix (i : ℕ) : IsClosed (↑(fixedAt H F i):Set H):= isClosed_eq (Τ i).continuous (1:H.Op).continuous
instance : CompleteSpace (stationary H F) := (show IsClosed (↑(stationary H F):Set H) by unfold stationary; rw [Submodule.coe_iInf]; exact isClosed_iInter (closedFix H F)).isComplete.completeSpace_coe

lemma point_blend (g : H.Op) (x : H) (n : ℕ) : mix g n x=birkhoffAverage ℂ g id n x:=by
  unfold mix birkhoffAverage birkhoffSum
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.coe_pow', id_eq]
lemma mean_summit (p : ∀ i, ‖F i‖≤1) (n : ℕ) (x : H) :
    Tendsto (fun i => mix (Τ n) i x) atTop (𝓝 ((fixedAt H F n).starProjection x)) :=
  (ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (Τ n) (blend_small H F p n) x).congr (fun i => (point_blend H _ x i).symm)
lemma mean_cost (g : H.Op) (p : ‖g‖≤1) (x : H) (n : ℕ) : ‖mix g n x‖≤ ‖x‖ := by
  have h₁ (n:ℕ) : ‖(g^n) x‖ ≤ ‖x‖:= by induction n with
    | zero=> rw [pow_zero]; exact le_rfl
    | succ n ih=> rw [pow_succ']; exact (g.le_opNorm ((g^n) x)).trans ((mul_le_of_le_one_left (norm_nonneg _) p).trans ih)
  rcases Nat.eq_zero_or_pos n with rfl|v
  · simp [mix]
  unfold mix; rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,norm_smul, norm_inv, norm_natCast]; rw [←div_eq_inv_mul,div_le_iff₀ (show 0 < (n:ℝ) by exact_mod_cast v)]
  exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>h₁ i)).trans_eq (by simp [mul_comm]))

lemma finish (p : ∀ i,‖F i‖≤1) (x : H) : Tendsto (fun n=>(fixedAt H F n).starProjection x) atTop (𝓝 ((stationary H F).starProjection x)) := Vacancy.falling _ (descending H F p) _ rfl _
end Hilb
end YM.CF.Buffered.Afterglow.Tower.Selection.Companies
