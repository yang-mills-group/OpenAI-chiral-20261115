import YM.CF.Lattice.Frame
import YM.Lattice.Support

/-! Cutoff projector exponential locality (entry and U-dependence).
Sup norm in U only over admissible sector; distance is in fermion lattice units.
Not an estimate on the determinant-line phase or fermion determinant. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Lat
open YM.Lattice
open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker Topology BigOperators
variable {N : Side} {K n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] opCStarAlgebra
set_option linter.unusedSectionVars false

/-- Costs measured from row anchor. -/
def within (x : Site N) (k : ℕ) : Set (Site N) := {y | separation x y ≤ k}
abbrev KField (N : Side) (K n : Type*) := RLink N K → Op (Tx N n)
structure Strict (A : KField N K n) (k : ℕ) : Prop where
  stops U x y (h : k < separation x.1 y.1) : A U x y=0
  localU (x y) : LocalOn (within x.1 k) (fun U => A U x y)
namespace Strict
variable {A B : KField N K n} {k l : ℕ}
lemma weak (h : Strict A k) (he : k ≤ l) : Strict A l := ⟨fun U x y hx => h.stops U x y (lt_of_le_of_lt he hx),
  fun x y U V ha => h.localU x y U V (fun e hi hj => ha e (le_trans (show _ ≤ k from hi) he) (le_trans (show _ ≤ k from hj) he))⟩
lemma plus (ha : Strict A k) (hb : Strict B k) : Strict (fun U => A U+B U) k :=
  ⟨fun U x y hx => by simp only [Matrix.add_apply,ha.stops U x y hx,hb.stops U x y hx, add_zero],
    fun x y U V h => by simpa only [Matrix.add_apply] using congrArg₂ (· + ·) (ha.localU x y U V h) (hb.localU x y U V h)⟩
lemma minus (ha : Strict A k) : Strict (fun U => -A U) k :=
  ⟨fun U x y hx => by simp only [Matrix.neg_apply,ha.stops U x y hx,neg_zero],
    fun x y U V h => by simpa only [Matrix.neg_apply] using congrArg Neg.neg (ha.localU x y U V h)⟩
lemma sb (ha : Strict A k) (hb : Strict B k) : Strict (fun U => A U-B U) k := by simp_rw [sub_eq_add_neg]; exact ha.plus hb.minus
lemma scale (ha : Strict A k) (r : ℝ) : Strict (fun U => r • A U) k :=
  ⟨fun U x y hx => by simp only [Matrix.smul_apply,ha.stops U x y hx, smul_zero],
    fun x y U V h => by simpa only [Matrix.smul_apply] using congrArg (r • ·) (ha.localU x y U V h)⟩
lemma unit (k) : Strict (fun _ : RLink N K => (1:Op (Tx N n))) k := by
  constructor
  · intro U x y hx; have hi : x ≠ y := by rintro rfl; simp at hx
    exact Matrix.one_apply_ne hi
  intro x y U V _; rfl
lemma null (k) : Strict (fun _ : RLink N K => (0:Op (Tx N n))) k :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
lemma times (ha : Strict A k) (hb : Strict B l) : Strict (fun U => A U * B U) (k+l) := by
  constructor
  · intro U x y h; rw [Matrix.mul_apply]; apply Finset.sum_eq_zero; intro z _
    by_cases e : separation x.1 z.1 ≤ k
    · rw [hb.stops U z y (by have hs := separation_triangle x.1 z.1 y.1; omega), mul_zero]
    rw [ha.stops U x z (by omega), zero_mul]
  intro x y U V h
  change (A U * B U) _ _ = _; simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro z _
  rw [show A U x z=A V x z from (ha.weak (Nat.le_add_right k l)).localU x z U V h]
  by_cases e : separation x.1 z.1 ≤ k
  · have ht : within z.1 l ⊆ within x.1 (k+l) := fun p hp =>
      (separation_triangle x.1 z.1 p).trans (Nat.add_le_add e hp)
    rw [show B U z y=B V z y from hb.localU z y U V fun a hl hi => h a (ht hl) (ht hi)]
  rw [ha.stops V _ _ (by omega)]; simp
lemma powers (ha : Strict A k) (j : ℕ) : Strict (fun U => A U ^ j) (j*k) := by
  induction j with
  | zero => simp only [zero_mul,pow_zero]; exact unit _
  | succ j ih => simp only [pow_succ, add_mul,one_mul]; exact ih.times ha
lemma collection {ι : Type*} (s : Finset ι) (X : ι → KField N K n)
    (h : ∀ i ∈ s, Strict (X i) k) : Strict (fun U => ∑ i ∈ s, X i U) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact null _
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).plus (ih (fun i hj => h i (Finset.mem_insert_of_mem hj)))
end Strict

variable [Group K]
variable (R : K →* UNI n) (cut : Site N)
lemma oneTouch (x : Site N) (i : Axis) : separation x (x+step i) ≤ 1 := by
  rw [separation_comm,separation,add_comm,add_sub_cancel_right]; exact pdist_step _
lemma shiftLocal (i : Axis) : Strict (fun U => shift R U cut i) 1 := by
  constructor
  · rintro U ⟨x,a⟩ ⟨y,b⟩ h
    have he : advance i x ≠ y := fun hy => not_lt_of_ge (oneTouch x i) (show 1 < separation x (advance i x) by rw [hy]; exact h)
    simp only [shift,jump_apply,if_neg he]
  rintro ⟨x,a⟩ ⟨y,b⟩ U V h
  have he := h ((x,i):Edge _) (show x∈within x 1 by simp [within]) (oneTouch x i)
  change shift _ _ _ _ _ _ = _; simp only [shift,jump_apply,hop,he]
lemma shiftStarLocal (i : Axis) : Strict (fun U => star (shift R U cut i)) 1 := by
  constructor
  · rintro U x y h; rw [separation_comm] at h; simp [(shiftLocal R cut i).stops U y x h]
  rintro ⟨x,a⟩ ⟨y,b⟩ U V h
  change star (shift _ _ _ _) _ _ = _
  simp only [Matrix.star_apply, shift,jump_apply]
  split <;> rename_i e
  · have hh : (y+step i: Site N)=x := e
    have hi := h ((y,i):Edge _) (show separation x y ≤ 1 from hh ▸ (separation_comm y (y+step i) ▸ oneTouch y i))
        (show y+step i ∈ within x 1 by simp [hh,within])
    simp only [hop,hi]
  rfl
lemma spinLocal (S : Op SpinIdx) : Strict (fun _ : RLink N K => spin N n S) 0 := by
  constructor
  · intro U x y h; have he : x.1≠y.1 := fun hx => by rw [hx,separation_self] at h; omega
    simp only [spin,jump_apply,Equiv.refl_apply,if_neg he]
  intro x y U V _; rfl
lemma Hlocal : Strict (fun U => (frame R U cut).H) 1 := by
  have h (i) : Strict (fun U => (frame R U cut).inc i) 1 := by
    have ht := shiftLocal R cut i
    have hs := shiftStarLocal R cut i
    apply Strict.plus
    · exact (Strict.unit _).sb ((ht.plus hs).scale _)
    have he := (spinLocal (K:=K) (N:=N) (n:=n) (gammaOp i)).times ((ht.sb hs).scale (1/2))
    rw [zero_add] at he; exact he
  have hb := (spinLocal (N:=N) (K:=K) (n:=n) grading).times ((Strict.unit _).minus.plus
    (Strict.collection Finset.univ _ (fun i _ => h i)))
  rw [zero_add] at hb; exact hb
lemma approximateLocal (k : ℕ) : Strict (fun U => approxP (frame R U cut).H k) (1+k*2) := by
  have hr := Hlocal R cut
  have hs : Strict (fun U => slack (frame R U cut).H) 2 := by
    have he := (Strict.unit _).sb ((hr.powers 2).scale (1/256))
    rw [mul_one] at he; exact he
  have ht (i) : i∈Finset.range k → Strict (fun U => rsTerm (frame R U cut).H i) (k*2) := fun h =>
    ((hs.powers i).scale _).weak (Nat.mul_le_mul_right _ (le_of_lt (Finset.mem_range.mp h)))
  exact ((Strict.unit _).plus ((hr.scale _).times (Strict.collection _ _ ht))).scale _ -- ht shape

variable [Nonempty n]
lemma cost_approx (U : RLink N K) (h : PlaqBound R U (1/60)) (x y : Tx N n) (k : ℕ) :
    ‖projector (frame R U cut).H x y - approxP (frame R U cut).H k x y‖ ≤ 256 * rho^k := by
  apply le_trans (norm_entry (projector (frame R U cut).H-approxP (frame R U cut).H k) x y)
  have hm := band R U cut h
  apply (projector_tail k hm.good rho_lt).trans
  calc
    _ ≤ (16/32)*(rho^k*(1-rho)⁻¹) := by
      apply mul_le_mul_of_nonneg_right (by gcongr; exact hm.bound) (mul_nonneg (pow_nonneg rho_pos.le _) (inv_nonneg.mpr (sub_nonneg.mpr rho_lt.le)))
    _ = _ := by rw [show (1-rho)⁻¹=512 by norm_num [rho]]; ring
/-- No plane waves or smooth links required. -/
theorem locality (U : RLink N K) (h : PlaqBound R U (1/60)) (x y : Tx N n) (k : ℕ) :
    (1+k*2 < separation x.1 y.1 → ‖projector (frame R U cut).H x y‖ ≤ 256*rho^k) ∧
      ∀ V, PlaqBound R V (1/60) → Agrees (within x.1 (1+k*2)) U V →
        ‖projector (frame R U cut).H x y-projector (frame R V cut).H x y‖ ≤ 512*rho^k := by
  have hl := approximateLocal R cut k
  have hm := cost_approx R cut U h x y k
  constructor
  · intro he
    simpa only [show approxP (frame R U cut).H k x y=0 from hl.stops U x y he,sub_zero] using hm
  intro V hv hh
  let P := fun V => projector (frame R V cut).H x y
  let F := fun V => approxP (frame R V cut).H k x y
  have hq : F U=F V := hl.localU x y U V hh
  calc
    _ = ‖P U-F U-(P V-F V)‖ := by rw [hq]; change ‖P U-P V‖ = _; rw [sub_sub_sub_cancel_right]
    _ ≤ 256*rho^k + 256*rho^k := (norm_sub_le _ _).trans (add_le_add hm (cost_approx R cut V hv x y k))
    _ = _ := by ring
end YM.CF.Lat
