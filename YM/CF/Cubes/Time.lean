import YM.CF.Cubes.Check

/-! Variation in prism parameter, constants at most polynomial in the block edge. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology Pointwise
attribute [local instance] opCStarAlgebra
variable {m B : Side} {U : Bkg (Domain m B)} {e d : ℝ}
lemma weight_s (q u : Sq) (i) : |starts q i-starts u i|≤3*‖q-u‖ := by
  have he (i : Row) : |q i-u i|≤ ‖q-u‖ := norm_le_pi_norm (q-u) i
  unfold starts; rw [←sum_sub_distrib,←Real.norm_eq_abs]
  apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i _=>he i)).trans
  rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right; exact_mod_cast (show (univ.filter (i < ·)).card≤3 from card_le_univ _); exact norm_nonneg _
lemma unroll (a b u v : ℝ) (w x : ℝ) : |Seg.seg a b w x-Seg.seg a b u v| ≤ |w-u|+|x-v| := by
  unfold Seg.seg; grind
lemma weight_score (q u : Sq) (i) (t) : |score B t q i-score B t u i| ≤ 7*‖q-u‖ := by
  apply (unroll ..).trans
  unfold ends; rw [add_sub_add_comm]
  have h := weight_s q u i
  have he : |q i-u i|≤ ‖q-u‖ := norm_le_pi_norm (q-u) i
  have H := abs_add_le (starts q i-starts u i) (q i-u i); linarith
lemma gold (q u : Sq) (a) (z) : |cash m B z q a-cash m B z u a| ≤ (B.val:ℝ)*(7*‖q-u‖) := by
  unfold cash; rw [←sum_sub_distrib,←Real.norm_eq_abs]; apply (norm_sum_le ..).trans (le_trans (sum_le_sum (fun i _=> weight_score _ _ _ _)) _)
  rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right
  · apply Nat.cast_le.mpr; apply (card_le_univ (ticks m B z _)).trans
    simp only [Coin,Fintype.card_fin]; have h := enoughWidth B; omega
  positivity
def variations (B : Side) := (4/low * (14*B.val*7))
lemma variation_pos (B : Side) : 0<variations B := by
  unfold variations; have he := low_p; have hB : 0 < (B.val:ℝ) := Nat.cast_pos.mpr B.property; positivity
lemma variations_le (s : ArrayF m) (q u : Sq) (g : prob q) (k : prob u) (he : 0≤e) (h : Guard U e) {r : Finset Row}
    (hv : Verified m B margin U s r) (hs : ∀ i∉r, q i=0) (hb : ∀ i∉r, u i=0) (hc : enoughV B e d) (z) :
    ‖paintV m B U s q z-paintV m B U s u z‖≤variations B * ‖q-u‖ := by
  unfold paintV variations; rw [mul_assoc (4/low)]
  apply (ren_near (prism_nonzero s g he h hv hs hc.1 z) (prism_nonzero s k he h hv hb hc.1 z)).trans
  apply mul_le_mul_of_nonneg_left
  · unfold paint; rw [←sum_sub_distrib]
    let R := bandS m B z q ∪ bandS m B z u
    have H : R.card≤14 := (card_union_le ..).trans (Nat.add_le_add (size_band g) (size_band k))
    rw [← sum_subset (subset_univ R)]; swap
    · intro a _ hx; obtain ⟨E,B'⟩ := (not_or.mp (show ¬ _ from fun h=>hx (mem_union.mpr h)))
      rw [outside E,outside B',zero_smul,sub_self]
    apply (norm_sum_le ..).trans; let X := (B.val:ℝ)*(7*‖q-u‖)
    apply le_trans _ (show ∑ i ∈ R, (fun _ => X) i ≤ _ from ?_)
    · apply sum_le_sum; intro a ha; rw [← sub_smul,norm_smul,Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left (freight_norm ..) (abs_nonneg _)).trans (by rw [mul_one]; exact gold ..)
    rw [sum_const,nsmul_eq_mul]
    unfold X; apply (mul_le_mul_of_nonneg_right (show (R.card:ℝ)≤14 by exact_mod_cast H) (by positivity)).trans; apply le_of_eq; ring
  have h := low_p; positivity
end YM.CF.Cube
