import YM.CF.Cubes.Ferry

/-! Neighbor bound uses anchor interpolation and the elementary cap. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology Pointwise
attribute [local instance] opCStarAlgebra
variable {m B N : Side} {U : Bkg (Domain m B)} {e : ℝ}
lemma lift_step (h : 3 ≤ N.val) (i : Axis) : lift (step i : Site N)=step i := by
  rw [lift_eq_iff, wrap_step]; refine ⟨rfl,fun j=>?_⟩; rw [step_apply]; split <;> omega
lemma step_gap (he : 0≤e) (h : Guard U e) (z) (a i v) (g : a∈active m B z) (k : a∈active m B (z+step i)) :
    ‖turn (U (z,i)) (launch m B U (z+step i) a 1 v)-launch m B U z a 1 v‖≤pot B e := by
  let x := address m B a; let y := z+step (S:=Per (Domain m B)) i; let W := march y x 1; let Y := march z x 1
  have hz : separation z x<B.val := node_dist g; have hy : separation y x<B.val := node_dist k
  have ho : lift (y-x)=lift (y-z)+lift (z-x) := by
    have hf := moves_lift hz hy
    rw [hf]; abel -- fix
  have hs : stop (0:Cover) (posDir i::W) = stop 0 Y := by
    simp only [stop, W,Y,Step.vec_pos,zero_add,march]
    have h := stop_trans (step i) 0 W; unfold W march at h; rw [route_end,add_zero] at h
    rw [route_end,h]
    have hh : lift (y-z)=step i := by
      unfold y; rw [add_sub_cancel_left, lift_step]; have h := enough m B; have e : 0<B.val := B.property; omega
    have he (p : Site (Domain m B)) (g : separation p x < B.val) : lift (x-p)= -lift (p-x) := by
      rw [lift_eq_iff]; refine ⟨by rw [map_neg,wrap_lift,neg_sub],?_⟩; intro j; rw [Pi.neg_apply]; have h := lifts_far g j; have he := enough m B; omega
    rw [he y hy,he z hz,ho,hh]; abel
  have H := near_hop he h.1 z _ _ hs
  rw [launch, launch, ← turn_seq]; apply (turn_price ..).trans
  rw [vote_unit,mul_one]; apply H.trans
  have ha : (W.length:ℝ) ≤ 4*B.val := by exact_mod_cast march_len y x 1 (by rw [separation_comm]; exact hy.le)
  have hb : (Y.length:ℝ) ≤ 4*B.val := by exact_mod_cast march_len z x 1 (by rw [separation_comm]; exact hz.le)
  have hp : 1 ≤ (B.val:ℝ) := by exact_mod_cast B.property
  simp only [pot,List.length_cons]; push_cast; rw [←add_mul]; apply mul_le_mul_of_nonneg_right _ he
  nlinarith [pow_le_pow_left₀ (by positivity) ha 2,pow_le_pow_left₀ (by positivity) hb 2]
lemma freight_gap (he : 0≤e) (h : Guard U e) (z) (a v) (g : a ∈ active m B z) (o) :
    ‖freight m B U z a v-launch m B U z a o v‖≤pot B e := avg_bound _ _ _ (fun i=>launch_gap he h g v i o)
lemma freight_norm (m B U z a v) : ‖freight m B U z a v‖ ≤ 1 := by
  simpa only [sub_zero,freight] using avg_bound (fun o=>launch m B U z a o v) 0 1 (fun i=>by rw [sub_zero,launch_norm])
lemma freight_cont (m B z a) : Continuous (fun t : Bkg (Domain m B) × Ballot => freight m B t.1 z a t.2) := by
  have hx : Continuous (fun t : Bkg (Domain m B) × Ballot=>∑ o, launch m B t.1 z a o t.2) := continuous_finsetSum _ (fun i _=>launch_cont ..)
  unfold freight; exact (continuous_const (y:=(Fintype.card Lattice.Order:ℝ)⁻¹)).smul hx
lemma ferry_step (he : 0≤e) (h : Guard U e) (z) (a i v) (g : a∈active m B z) (k : a∈active m B (z+step i)) :
    ‖turn (U (z,i)) (freight m B U (z+step i) a v)-freight m B U z a v‖≤3*pot B e := by
  let p := launch m B U z a 1 v
  let q := launch m B U (z+step i) a 1 v
  apply (norm_sub_le_norm_sub_add_norm_sub _ p _).trans
  rw [show 3*pot B e=pot B e+pot B e+pot B e by ring]
  apply add_le_add ((norm_sub_le_norm_sub_add_norm_sub _ (turn (U (z,i)) q) _).trans (add_le_add _ (step_gap he h z a i v g k)))
  · rw [norm_sub_rev]; exact freight_gap he h _ _ _ g 1
  · rw [← turn_sub,turn_norm]; exact freight_gap he h _ _ _ k 1
variable (m B)
def paint (U : Bkg (Domain m B)) (s : ArrayF m) (q : Sq) (z : Site (Domain m B)) :=
    ∑ i : Spot m, cash m B z q i • freight m B U z i.1 (s i)
lemma cash_step {U : Bkg (Domain m B)} {q : Sq} (g : prob q) (s : ArrayF m) (i) (z : Site (Domain m B)) (he : 0≤e) (h : Guard U e) (a : Spot m) :
    ‖cash m B z q a • freight m B U z a.1 (s a) - turn (U (z,i))
      (cash m B (z+step i) q a • freight m B U (z+step i) a.1 (s a))‖ ≤ 1/(width B:ℝ) + 3*pot B e := by
  let y := z+step (S:=Per (Domain m B)) i; let p := freight m B U z a.1 (s a); let k := U (z,i); let r := freight m B U y a.1 (s a); let t := cash m B z q a; let w := cash m B y q a
  have hx := freight_norm m B U z a.1 (s a); change ‖p‖≤1 at hx
  have hy : ‖turn k r‖≤1 := by rw [turn_norm]; exact freight_norm ..
  have hp : 0≤pot B e := by unfold pot; positivity
  rw [turn_mul]; change ‖t • p - w • turn k r‖≤ _
  have ht : 0≤t := cash_nonneg ..; have hw : 0≤w := cash_nonneg ..; have hh : |t-w| ≤ 1/(width B:ℝ) := cash_lips ..
  by_cases hu : a∈bandS m B y q
  · by_cases hl : a∈bandS m B z q
    · have HK : ‖p-turn k r‖≤3*pot B e := by rw [norm_sub_rev]; exact ferry_step he h _ _ _ _ (spot_hit hl) (spot_hit hu)
      have hm : w≤1 := (single_le_sum (f:=cash m B y q) (fun j _=>cash_nonneg ..) (mem_univ a)).trans (le_of_eq (cash_sum _ _ _ _ g))
      apply (norm_sub_le_norm_sub_add_norm_sub _ (w • p) _).trans
      rw [←sub_smul,←smul_sub,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_of_nonneg hw]
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans (by rw [mul_one]; exact hh)
      exact (mul_le_mul hm HK (norm_nonneg _) (by norm_num)).trans (by rw [one_mul])
    have H : t=0 := outside hl; rw [H,zero_sub,abs_neg,abs_of_nonneg hw] at hh
    rw [H,zero_smul,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hw]
    exact (mul_le_mul_of_nonneg_left hy hw).trans (by rw [mul_one]; linarith)
  have H : w=0 := outside hu; rw [H,sub_zero,abs_of_nonneg ht] at hh
  rw [H,zero_smul,sub_zero,norm_smul,Real.norm_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left hx ht).trans (by rw [mul_one]; linarith)
lemma paint_bound {U : Bkg (Domain m B)} (s : ArrayF m) {q : Sq} (g : prob q) (z : Site (Domain m B)) : ‖paint m B U s q z‖≤1 := by
  apply (norm_sum_le ..).trans
  rw [←cash_sum m B z q g]; apply sum_le_sum; intro i _; rw [norm_smul,Real.norm_of_nonneg (cash_nonneg ..)]; exact (mul_le_mul_of_nonneg_left (freight_norm ..) (cash_nonneg ..)).trans (by simp)
lemma turn_sum {I : Type*} (k : E) (s : Finset I) (f : I → Vect) : turn k (∑ i∈s, f i)=∑ i∈s, turn k (f i) := map_sum (spinV k).toLinearMap ..
lemma paint_gap {U : Bkg (Domain m B)} (s : ArrayF m) {q : Sq} (g : prob q) (z : Site (Domain m B)) (he : 0≤e) (h : Guard U e) (i : Axis) :
    ‖turn (U (z,i)) (paint m B U s q (z+step i))-paint m B U s q z‖ ≤ 14*(1/(width B:ℝ)+3*pot B e) := by
  rw [norm_sub_rev,paint,paint,turn_sum,←sum_sub_distrib]
  let R := bandS m B z q ∪ bandS m B (z+step i) q
  have ht : R.card≤14 := (card_union_le ..).trans (Nat.add_le_add (size_band g) (size_band g))
  rw [←sum_subset (subset_univ R)]; swap
  · intro a _ hl; obtain ⟨H,E⟩ := (not_or.mp (show ¬ _ from fun h=>hl (mem_union.mpr h)))
    rw [outside H,outside E,zero_smul,zero_smul,turn,map_zero,sub_self]
  apply (norm_sum_le ..).trans
  apply (sum_le_sum (fun a _=>cash_step m B g s i z he h a)).trans
  rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right (by exact_mod_cast ht); unfold pot; positivity
end YM.CF.Cube
