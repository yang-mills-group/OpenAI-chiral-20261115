import YM.CF.Cubes.Nest

/-! partition of unity with neighbor bound -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat Finset
open scoped BigOperators
variable {m B : Side}

def ticks (m B : Side) (z : Site (Domain m B)) (a : Index m) := univ.filter (fun t => ballot m B z a t)
def weight (m B : Side) (z : Site (Domain m B)) (a : Index m) : ℝ := (ticks m B z a).card / (width B:ℝ)
lemma w_nonneg (m B z a) : 0 ≤ weight m B z a := by unfold weight; positivity
lemma w_pos {z a} : 0 < weight m B z a ↔ a∈active m B z := by
  have h : (0:ℝ)< width B := by exact_mod_cast width_pos B
  unfold weight; rw [lt_div_iff₀ h,zero_mul,Nat.cast_pos,card_pos,active_iff]
  simp [ticks, Finset.Nonempty]
lemma w_sum (m B z) : ∑ a, weight m B z a=1 := by
  have h : ∑ a:Index m, (ticks m B z a).card=width B := by
    have he : univ.biUnion (ticks m B z) = univ := by ext t; simp only [mem_biUnion,mem_univ,true_and,
                                                                     ticks,mem_filter,iff_true]; exact some_ballot ..
    rw [←card_biUnion,he,card_univ,Fintype.card_fin]; intro a _ b _ l
    exact disjoint_left.mpr fun i hi hx => l (((picked_iff).mp (mem_filter.mp hi).2).trans ((picked_iff).mp (mem_filter.mp hx).2).symm)
  unfold weight; rw [← sum_div,← Nat.cast_sum,h,div_self]; exact_mod_cast (width_pos B).ne'
lemma w_zero {z a} (h : a∉active m B z) : weight m B z a=0 := le_antisymm (not_lt.mp (fun H=>h (w_pos.mp H))) (w_nonneg ..)

lemma radius_inj (m B a) : Function.Injective (radius m B a) := by
  intro t u h; unfold radius at h; have he := t.isLt; have hg := u.isLt
  apply Fin.ext; split at h <;> omega
lemma disappear {x y : Site (Domain m B)} (j : Axis) (h₁ : delta1 (Domain m B) (x j) (y j) ≤ 1) (h₂ : ∀ i≠j, x i=y i)
    (a : Index m) : ((ticks m B x a) \ ticks m B y a).card ≤ 1 := by
  let b := high m B (a j); let d := delta1 (Domain m B) (x j) b
  have he (t) (h : t∈ (ticks m B x a) \ ticks m B y a) : radius m B (a j) t = d := by
    obtain ⟨hx,hy⟩ := mem_sdiff.mp h
    have hx : ballot m B x a t := (mem_filter.mp hx).2
    have hl : d ≤ radius m B (a j) t := hx j
    by_contra g
    have gt : d<radius m B (a j) t := lt_of_le_of_ne hl (by symm; exact g)
    apply hy; rw [ticks,mem_filter]; refine ⟨mem_univ _,?_⟩; intro i
    by_cases hi : i=j
    · subst i; have he := d_one_triangle (N:=Domain m B) (y j) (x j) b -- m?
      rw [d_sym (x j) (y j)] at he
      exact le_trans he (by change _+d≤_; omega)
    rw [← h₂ i hi]; exact hx i
  exact card_le_one.mpr (fun i hi j hj => radius_inj m B (a _) ((he i hi).trans (he j hj).symm))
lemma shift_dis (z : Site (Domain m B)) (a) (j) : |weight m B (z+step j) a-weight m B z a| ≤ 1/(width B:ℝ) := by
  let X := ticks m B z a; let W := z+step (S:=Per (Domain m B)) j; let Y := ticks m B W a
  have h₁ : delta1 _ (W j) (z j) ≤ 1 := by simp [W,links_d (m:=m) (B:=B)]
  have h₂ (i) (h:i≠j) : W i=z i := by simp [W,h]
  have ha : (Y \ X).card ≤ 1 := disappear j h₁ h₂ a
  have hb : (X \ Y).card ≤ 1 := disappear j (show delta1 (Domain m B) (z j) (W j)≤1 by rw [d_sym]; exact h₁) (fun i hi => (h₂ i hi).symm) a
  have hx := card_sdiff_add_card_inter Y X; have hy := card_sdiff_add_card_inter X Y; rw [inter_comm X Y] at hy
  unfold weight; rw [←sub_div,abs_div,abs_of_nonneg (show (0:ℝ)≤width B from Nat.cast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  change |(Y.card:ℝ)-X.card| ≤ 1; rw [abs_le,le_sub_iff_add_le,sub_le_iff_le_add]
  constructor
  · have h : (X.card:ℝ)≤Y.card+1 := by exact_mod_cast (show X.card ≤ Y.card+1 by omega)
    linarith
  exact_mod_cast (show Y.card ≤ 1+X.card by omega)
end YM.CF.Cube
