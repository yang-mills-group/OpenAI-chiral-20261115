import YM.CF.Cubes.Tally
import YM.CF.Cubes.Gram

/-! Flags, up to three interpolation rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU
open scoped Matrix.Norms.L2Operator MatrixOrder Topology Pointwise
attribute [local instance] opCStarAlgebra
variable {m B N : Side}

def march (x y : Site N) (o : Lattice.Order) := route 0 (lift (y-x)) o
lemma stop_wrap (z : Cover) (x : Site N) (l : Walk) : stop (x+wrap N z) l=x+wrap N (stop z l) := by
  induction l generalizing z x with
  | nil => rfl
  | cons i l ih => simp only [stop,add_assoc]; rw [← wrap_vec N i,← map_add,ih]
lemma arrive (x y : Site N) (o : Lattice.Order) : stop x (march x y o)=y := by
  unfold march
  have he := stop_wrap 0 x (route 0 (lift (y-x)) o); rw [route_end,map_zero,add_zero,wrap_lift,add_sub_cancel] at he -- tune
  exact he
lemma travel_cont {K R : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [AddCommGroup R] [One R] (x : Four R) (w : Walk) :
    Continuous (fun U : Links R K => travel U x w) := by
  induction w generalizing x with
  | nil => exact continuous_const
  | cons d w ih =>
    simp only [travel,Step.read]; split <;> first | exact (continuous_apply _).mul (ih _) | exact (continuous_apply _).inv.mul (ih _)
lemma march_len (x y : Site N) (o : Lattice.Order) {t : ℕ} (h : separation y x≤t) : (march x y o).length≤4*t := by
  apply route_size
  intro i; simp only [Pi.zero_apply,sub_zero]; exact (component_le _ _).trans h

def parcel (m B : Side) (U : Bkg (Domain m B)) (x y : Index m) (o : Lattice.Order) := travel U (address m B x) (march (address m B x) (address m B y) o)
abbrev Row := Fin 3
abbrev Spot (m : Side) := Index m × Row
abbrev Ramp (m : Side) := Spot m × Lattice.Order
abbrev Field (m : Side) := Index m → Ballot
abbrev ArrayF (m : Side) := Spot m → Ballot
/-- Directions of progress in a flag. Tracks vertex dimension and row. -/
def Prev (m : Side) (a b : Spot m) := Fits m a.1 b.1 ∧ a.2≤b.2 ∧ a≠b
lemma prev_sign {a b : Spot m} (h : Prev m a b) : degree m a.1+a.2.val < degree m b.1+b.2.val := by
  rcases h with ⟨f,k,l⟩
  by_cases g : a.1=b.1
  · rw [g]; exact Nat.add_lt_add_left (Fin.lt_def.mp (lt_of_le_of_ne k (fun h=>l (Prod.ext g h)))) _
  exact Nat.add_lt_add_of_lt_of_le (fits_degree f g) (Fin.le_iff_val_le_val.mp k)
lemma prev_flow {a b c : Spot m} (h : Prev m a b) (g : Prev m b c) : Prev m a c :=
  ⟨fits_trans h.1 g.1, h.2.1.trans g.2.1, fun k => lt_irrefl _ ((prev_sign h).trans (prev_sign g) |>.trans_le (le_of_eq (by rw [k])))⟩
def Moves (m : Side) (a : Spot m) : List (Ramp m) → Prop
  | [] => True
  | r::l => Prev m r.1 a ∧ Moves m r.1 l
lemma moves_tail {a r l} (h : Moves m a (r::l)) : Moves m r.1 l := h.2
lemma moves_len {a l} (h : Moves m a l) : l.length≤degree m a.1+a.2.val := by
  induction l generalizing a with
  | nil => exact Nat.zero_le _
  | cons r l ih => exact (Nat.add_le_add_right (ih (moves_tail h)) _).trans (Nat.succ_le_of_lt (prev_sign (show Prev m _ _ from h.1)))
lemma total_len {a l} (h : Moves m a l) : l.length≤6 := (moves_len h).trans (Nat.add_le_add (degree_le ..) (show _ from Nat.le_of_lt_succ a.2.isLt))
lemma move_mem {a l} (h : Moves m a l) (r : Ramp m) (g : r∈l) : Prev m r.1 a := by
  induction l generalizing a with
  | nil => simp at g
  | cons i l ih => rcases List.mem_cons.mp g with k|k; subst r; exact h.1; exact prev_flow (ih (moves_tail h) k) h.1

def scopeF (m : Side) (x : Index m) := (faces m x ×ˢ (Finset.univ : Finset Row)) ×ˢ (Finset.univ : Finset Lattice.Order)
-- reusable count of lower flags
def words {I : Type*} [DecidableEq I] (s : Finset I) : ℕ → Finset (List I)
  | 0 => {[]}
  | n+1 => insert [] ((s ×ˢ (words s n)).image (fun p => p.1 :: p.2))
def wordsCount (M : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => M*wordsCount M n + 1
lemma count_words {I : Type*} [DecidableEq I] {s : Finset I} {M : ℕ} (h : s.card≤M) (n : ℕ) :
    (words s n).card ≤ wordsCount M n := by
  induction n with
  | zero => exact le_of_eq (Finset.card_singleton _)
  | succ n ih => rw [words,wordsCount]; apply Finset.card_insert_le .. |>.trans; apply Nat.add_le_add_right; apply le_trans (Finset.card_image_le); rw [Finset.card_product]; exact Nat.mul_le_mul h ih
lemma words_hit {I : Type*} [DecidableEq I] (s : Finset I) {l : List I} (h : ∀ i∈l, i∈s) (n : ℕ) (g : l.length≤n) : l∈ words s n := by
  induction n generalizing l with
  | zero => have he : l=[] := List.eq_nil_of_length_eq_zero (by omega); rw [he]; exact Finset.mem_singleton.mpr rfl
  | succ n ih =>
    cases l with
    | nil => exact Finset.mem_insert_self ..
    | cons i l =>
      rw [words,Finset.mem_insert]; right; apply Finset.mem_image.mpr
      exact ⟨(i,l),Finset.mem_product.mpr ⟨h i (by simp), ih (fun i' hi=>h i' (List.mem_cons_of_mem _ hi)) (by simpa using g)⟩,rfl⟩
open Finset
def InRows (r : Finset Row) (l : List (Ramp m)) := ∀ i∈l, i.1.2∈r
instance (a l) : Decidable (Moves m a l) := Classical.propDecidable _
instance (r) (l : List (Ramp m)) : Decidable (InRows r l) := Classical.propDecidable _
def permits (m : Side) (a : Spot m) (r : Finset Row) := (words (scopeF m a.1) 6).filter (fun l=> Moves m a l ∧ InRows r l)
lemma permits_iff {a r l} : l ∈ permits m a r ↔ Moves m a l ∧ InRows r l := by
  unfold permits; classical -- custom DecidablePred
  rw [mem_filter]; exact ⟨fun h=>h.2,fun h=>⟨words_hit _ (fun i hi=>by
    simp only [scopeF,mem_product,mem_univ,and_true,faces,mem_filter,true_and]; exact (move_mem h.1 i hi).1) _ (total_len h.1),h⟩⟩
def budgetW := wordsCount ((box 1).card * Fintype.card Row * Fintype.card Lattice.Order) 6
lemma permits_cap (m a r) : (permits m a r).card ≤ budgetW := by
  unfold permits; apply (card_filter_le ..).trans; apply count_words; simp only [scopeF,card_product,card_univ]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (faces_bound ..))

def train (m B : Side) (U : Bkg (Domain m B)) (s : ArrayF m) (x : Index m) : List (Ramp m) → List Vect
  | [] => []
  | ⟨w,o⟩::l => ((s w).val :: train m B U s w.1 l).map (turn (parcel m B U x w.1 o))
lemma train_len (m B U s x l) : (train m B U s x l).length=l.length := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => cases i; rw [train,List.length_map,List.length_cons,List.length_cons,ih]
/-- Array constraint at a top-row spot. -/
def Check (m B : Side) (e : ℝ) (U : Bkg (Domain m B)) (s : ArrayF m) (r : Finset Row) (a : Spot m) :=
    ∀ l∈permits m a r, e < ‖restrain e (train m B U s a.1 l) (s a).val‖
def Verified (m B : Side) (e : ℝ) (U : Bkg (Domain m B)) (s : ArrayF m) (r : Finset Row) := ∀ a : Spot m, a.2∈r → Check m B e U s r a
lemma thick_train {U s r a l e} (h : Verified m B e U s r) (g : l ∈ permits m a r) (he : a.2∈r) :
    Thick e ((s a).val :: train m B U s a.1 l) := by
  constructor
  · exact h a he l g
  induction l generalizing a with
  | nil => trivial
  | cons i l ih =>
    rcases i with ⟨w,o⟩; have H := permits_iff.mp g
    rw [train,thick_turn_iff]
    have g' : l∈permits m w r := permits_iff.mpr ⟨H.1.2, fun j hj=> H.2 j (List.mem_cons_of_mem _ hj)⟩
    have hw : w.2∈r := H.2 _ List.mem_cons_self
    exact ⟨h w hw l g',ih g' hw⟩ -- tune
lemma train_eq (m B U s x l) (t : ArrayF m) (h : ∀ r : Ramp m, r∈l → t r.1=s r.1) : train m B U t x l=train m B U s x l := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih => cases r with | mk w o => rw [train,train,ih _ (fun i hi=>h i (List.mem_cons_of_mem _ hi)), show t w = s w from h (w,o) (by simp)]
end YM.CF.Cube
