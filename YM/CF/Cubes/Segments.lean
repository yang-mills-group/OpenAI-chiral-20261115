import YM.CF.Cubes.Flag

/-! Ordered interval overlap weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology BigOperators Pointwise
attribute [local instance] opCStarAlgebra
variable {m B : Side}

namespace Seg
def seg (l u L U : ℝ) := max 0 (min U u - max L l)
lemma ge (l u L U) : 0≤seg l u L U := le_max_left ..
lemma seg_sym (l u L U) : seg L U l u=seg l u L U := by unfold seg; rw [min_comm u,max_comm l]
lemma pos (l u L U) : 0<seg l u L U ↔ max L l<min U u := by simp [seg]; tauto
lemma zeroL (a L U) : seg a a L U=0 := by
  apply le_antisymm _ (ge ..); unfold seg; apply max_le le_rfl; have he := min_le_right U a; have hg := le_max_right L a; linarith
lemma incr (a b c l u : ℝ) (h : a≤b) (g : b≤c) (e : l≤u) : seg a b l u+seg b c l u=seg a c l u := by
  unfold seg; grind -- min max
lemma full (a b l u : ℝ) (h : a≤b) (g : l≤a) (t : b≤u) : seg a b l u=b-a := by rw [seg,max_eq_right g,min_eq_right t,max_eq_right (sub_nonneg.mpr h)]
lemma size (a b l u : ℝ) (h : a≤b) : seg a b l u≤ b-a := max_le (sub_nonneg.mpr h) (sub_le_sub (min_le_right ..) (le_max_right ..))
@[fun_prop] lemma seg_cont (a b : ℝ) : Continuous (fun t : ℝ×ℝ=>seg a b t.1 t.2) := by unfold seg; fun_prop
end Seg
open Seg

abbrev Sq := Row→ℝ
def prob (q : Sq) := (∀ i,0≤q i) ∧ ∑ i,q i=1
def starts (q : Sq) (i : Row) := ∑ j∈ univ.filter (fun j=> i < j), q j
def ends (q : Sq) (i : Row) := starts q i+q i
@[fun_prop] lemma starts_cont (i : Row) : Continuous (fun q=>starts q i) := by unfold starts; fun_prop
@[fun_prop] lemma ends_cont (i : Row) : Continuous (fun q=>ends q i) := by unfold ends; fun_prop
lemma p_parts (q : Sq) (h : prob q) : ends q 0=1 ∧ ends q 1=starts q 0 ∧ ends q 2=starts q 1 ∧ starts q 2=0 := by
  have h0 := h.2
  simp only [Row,Fin.sum_univ_succ] at h0
  simp [ends,starts,sum_filter,Row,Fin.sum_univ_succ] at * -- tune
  grind
lemma pos_s (q : Sq) (h : prob q) (i : Row) : starts q i ≤ ends q i := by unfold ends; exact le_add_of_nonneg_right (h.1 i)
lemma lower_s (q : Sq) (h : prob q) (i : Row) : 0≤starts q i := sum_nonneg (fun j _=>h.1 j)
lemma sorted_r (q : Sq) (h : prob q) (i j : Row) (hij : i < j) : ends q j≤starts q i := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := p_parts q h
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp only [Fin.isValue, Fin.mk_one] at * -- tune
  all_goals first | exact le_of_eq h₂ | exact le_of_eq h₃ | exact h₃.le.trans ((pos_s _ h 1).trans h₂.le) | omega
lemma upper_s (q : Sq) (h : prob q) (i : Row) : ends q i ≤ 1 := by
  by_cases g:i=0
  · rw [g,(p_parts _ h).1]
  exact (sorted_r q h 0 i (Fin.pos_iff_ne_zero.mpr g)).trans ((pos_s q h _).trans (p_parts q h).1.le)
def mark (B : Side) (k : ℕ) : ℝ := k/(width B:ℝ)
def score (B : Side) (t : Coin B) (q : Sq) (i : Row) := seg (mark B t.val) (mark B (t.val+1)) (starts q i) (ends q i)
lemma mzero (B) : mark B 0=0 := by simp [mark]
lemma mwidth (B) : mark B (width B)=1 := by
  have h : (width B:ℝ)>0 := by exact_mod_cast width_pos B
  simp [mark,h.ne']
lemma mmono (B) : Monotone (mark B) := fun i j h=> div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg _)
lemma price (B t q i) : score B t q i≤1/(width B:ℝ) :=
  (size _ _ _ _ (mmono B (Nat.le_succ _))).trans (le_of_eq (by simp [mark,add_div]))
lemma price_nonneg (B t q i) : 0≤score B t q i := Seg.ge ..
lemma ticks_sum (B : Side) (l u : ℝ) (g : 0≤l) (v : l≤u) (w : u≤1) :
    ∑ i:Coin B, seg (mark B i.val) (mark B (i.val+1)) l u=u-l := by
  have h (n : ℕ) : ∑ i∈range n, seg (mark B i) (mark B (i+1)) l u=seg 0 (mark B n) l u := by
    induction n with
    | zero => simp [mzero,zeroL]
    | succ n ih => rw [sum_range_succ,ih,incr _ _ _ _ _ (by unfold mark; positivity) (mmono B (Nat.le_succ _)) v]
  rw [show (∑ i:Coin B, _) = ∑ i∈range (width B), seg (mark B i) (mark B (i+1)) l u from (sum_range ..).symm] -- check name
  rw [h,mwidth,seg_sym,full _ _ _ _ v g w]
lemma row_sum (B : Side) (q) (h : prob q) (i) : ∑ t:Coin B, score B t q i=q i := by
  unfold score; rw [ticks_sum B _ _ (lower_s q h i) (pos_s q h i) (upper_s q h i),ends,add_sub_cancel_left] -- placeholders
lemma score_same (B : Side) (t : Coin B) (q : Sq) (i) (h : q i=0) : score B t q i=0 := by unfold score; rw [seg_sym,ends,h,add_zero,zeroL]
@[fun_prop] lemma score_cont (B t i) : Continuous (fun q=>score B t q i) := by unfold score seg; fun_prop
end YM.CF.Cube
