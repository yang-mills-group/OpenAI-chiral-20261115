import YM.CF.Cubes.Segments

/-! Blending on faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology BigOperators
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def cash (m B : Side) (z : Site (Domain m B)) (q : Sq) (a : Spot m) := ∑ t∈ticks m B z a.1, score B t q a.2
def bandS (m B : Side) (z : Site (Domain m B)) (q : Sq) := univ.filter (fun a => 0 < cash m B z q a)
lemma cash_nonneg (m B z q a) : 0≤cash m B z q a := sum_nonneg (fun _ _=>price_nonneg ..)
lemma count_row (z : Site (Domain m B)) (q) (h : prob q) (i : Row) : ∑ a:Index m, cash m B z q (a,i) = q i := by
  unfold cash; simp_rw [ticks,sum_filter,picked_iff]; rw [sum_comm,←row_sum B q h i]
  apply sum_congr rfl; intro t _; simp
lemma cash_sum (m B z q) (h : prob q) : ∑ a, cash m B z q a=1 := by rw [Fintype.sum_prod_type,sum_comm]; simp_rw [count_row z q h]; exact h.2
lemma empty_cash {q i} (h : q i=0) (z : Site (Domain m B)) (a : Index m) : cash m B z q (a,i)=0 := sum_eq_zero (fun x _=>score_same B x q i h)
@[fun_prop] lemma cash_cont (m B z a) : Continuous (fun q => cash m B z q a) := by unfold cash; fun_prop
lemma outside {z q a} (h : a ∉ bandS m B z q) : cash m B z q a=0 :=
  le_antisymm (not_lt.mp (fun g=>h (mem_filter.mpr ⟨mem_univ _,g⟩))) (cash_nonneg ..)
lemma has_bandS (m B z q) (h : prob q) : (bandS m B z q).Nonempty := by
  by_contra! g
  have he := cash_sum m B z q h; rw [sum_eq_zero (fun i _=>outside (m:=m) (B:=B) (z:=z) (q:=q) (by rw [g]; simp))] at he; exact zero_ne_one he
lemma cash_vote {z q a} (h : a∈bandS m B z q) : ∃ t∈ticks m B z a.1, 0<score B t q a.2 := by
  by_contra! g; exact not_le_of_gt ((mem_filter.mp h).2) (sum_nonpos g)
lemma spot_hit {z q a} (h : a∈bandS m B z q) : a.1∈active m B z := by obtain ⟨t,g,-⟩ := cash_vote h; exact (active_iff ..).mpr ⟨_,(mem_filter.mp g).2⟩
def valS (m : Side) (i : Spot m) := degree m i.1 + i.2.val
lemma precede (q : Sq) (h : prob q) (a b : Coin B) (t u : Row) (e : a < b) (g : 0<score B a q t) (l : 0<score B b q u) : u≤t := by
  by_contra! he
  have H : ends q u ≤ starts q t := sorted_r q h _ _ he
  have hi := lt_of_lt_of_le ((Seg.pos ..).mp g) (min_le_right ..)
  have hz : starts q t < mark B (a.val+1) := lt_of_le_of_lt (le_max_left ..) hi
  have ht := lt_of_lt_of_le ((Seg.pos ..).mp l) (min_le_left ..)
  have hl : mark B b.val < ends q u := lt_of_le_of_lt (le_max_right ..) ht
  have hk := mmono B (show a.val+1 ≤ b.val from e); linarith
lemma arc {z q a b} (g : prob q) (h : a∈bandS m B z q) (hk : b∈bandS m B z q) (e : a≠b) :
    Prev m a b ∨ Prev m b a := by
  obtain ⟨t₁,H,H₁⟩ := cash_vote h; obtain ⟨t₂,J,J₁⟩ := cash_vote hk
  have heq := picked_iff.mp (show ballot m B z a.1 t₁ from (mem_filter.mp H).2)
  have heq' := picked_iff.mp (show ballot m B z b.1 t₂ from (mem_filter.mp J).2)
  rcases lt_trichotomy t₁ t₂ with he|he|he
  · right; refine ⟨?_,precede _ g _ _ _ _ he H₁ J₁,e.symm⟩; rw [heq,heq']; exact cmp_select _ _ _ he.le
  · subst t₁
    unfold Prev; rw [heq,heq']; exact (le_total a.2 b.2).imp (fun k=>⟨fits_id _ _,k,e⟩) (fun k=>⟨fits_id _ _,k,e.symm⟩)
  left; refine ⟨?_,precede _ g _ _ _ _ he J₁ H₁,e⟩; rw [heq,heq']; exact cmp_select _ _ _ he.le
lemma size_band {z q} (h : prob q) : (bandS m B z q).card ≤ 7 := by
  have he : Set.InjOn (valS m) (bandS m B z q) := by
    intro a ha b hb e; by_contra g; exact (arc h ha hb g).elim (fun l=>(prev_sign l).ne e) (fun l=>(prev_sign l).ne e.symm)
  rw [←card_image_of_injOn he]; apply (card_le_card (t:=range 7) _).trans (by simp only [card_range,le_refl])
  intro i hi; obtain ⟨a,-,rfl⟩ := mem_image.mp hi
  apply mem_range.mpr; exact lt_of_le_of_lt (Nat.add_le_add (degree_le m a.1) (show a.2.val≤2 from Nat.le_of_lt_succ a.2.isLt)) (by norm_num)
lemma dirac_prob (i : Row) : prob (Pi.single i 1) := ⟨fun a=>by simp [Pi.single_apply]; split <;> norm_num,by simp⟩
lemma dirac_score (i : Row) (t : Coin B) : score B t (Pi.single i 1) i=1/(width B:ℝ) := by
  have he : starts (Pi.single i 1) i=0 := sum_eq_zero (fun a ha=> by
    have g := (mem_filter.mp ha).2; simp only [Pi.single_apply]; exact if_neg (LT.lt.ne' g))
  rw [score,ends,he,Pi.single_eq_same,zero_add,Seg.full]
  · simp [mark,add_div]
  · exact mmono B (Nat.le_succ _)
  · unfold mark; positivity
  exact (mmono B (show t.val+1≤width B from t.isLt)).trans (le_of_eq (mwidth _))
lemma dirac_cash (i : Row) (z : Site (Domain m B)) (a : Index m) : cash m B z (Pi.single i 1) (a,i)=weight m B z a := by unfold cash; dsimp only; simp [dirac_score,weight,div_eq_mul_inv]
lemma cash_lips (z : Site (Domain m B)) (j : Axis) (q : Sq) (a : Spot m) : |cash m B z q a-cash m B (z+step j) q a| ≤ 1/(width B:ℝ) := by
  let W := z+step (S:=Per (Domain m B)) j; let X := ticks m B z a.1; let Y := ticks m B W a.1
  have h₁ : delta1 _ (W j) (z j)≤1 := by simp [W,links_d (m:=m) (B:=B)]
  have h₂ (i) (h:i≠j) : W i=z i := by simp [W,h]
  have he : (Y \ X).card ≤1 := disappear j h₁ h₂ a.1
  have ht : (X \ Y).card ≤1 := disappear j (show delta1 (Domain m B) (z j) (W j)≤1 by rw [d_sym]; exact h₁) (fun i hi=>(h₂ i hi).symm) a.1
  let f (t) := score B t q a.2
  let r : ℝ := 1/width B
  have pos (X : Finset (Coin B)) : 0 ≤ ∑ i∈X, f i := sum_nonneg (fun i _ => price_nonneg ..)
  have neg (X : Finset (Coin B)) (h : X.card≤1) : ∑ i∈X, f i ≤ r := by
    apply (sum_le_sum (fun i _=>price B i q a.2)).trans; rw [sum_const,nsmul_eq_mul]; change _*r≤r
    apply (mul_le_mul_of_nonneg_right (show (X.card:ℝ)≤1 from by exact_mod_cast h) (show 0≤r by unfold r; positivity)).trans; rw [one_mul]
  change |(∑ i∈X, f i)-(∑ i∈Y, f i)| ≤ r
  have HS (X Y : Finset (Coin B)) : ∑ i∈X, f i=(∑ i∈X \ Y, f i)+(∑ i∈X ∩ Y, f i) := by
    nth_rw 1 [← sdiff_union_inter X Y]; rw [sum_union]; exact disjoint_left.mpr (fun i hi hj => (mem_sdiff.mp hi).2 (mem_inter.mp hj).2)
  rw [HS X Y, HS Y X, inter_comm Y X,add_sub_add_right_eq_sub,abs_le]
  constructor <;> linarith [pos (X \ Y), pos (Y \ X), neg (Y \ X) he, neg (X \ Y) ht]
end YM.CF.Cube
