/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Support.Ball

/-! Compress a power with support convergence. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {A B : Op I} {r k v : ℕ} {a d K C : ℝ}
lemma FiniteOp.oneOp (v) : FiniteOp b v 1 := by intro i j h; by_cases g:i=j; rw [g,b.F.reflex] at h; omega; simp [g]
lemma FiniteOp.weak (h : FiniteOp b r A) (g : r≤k) : FiniteOp b k A := fun i j e=>h i j (lt_of_le_of_lt g e)
lemma FiniteOp.times (h : FiniteOp b r A) (g : FiniteOp b k B) : FiniteOp b (r+k) (A*B) := by
  intro i j e; rw [Matrix.mul_apply, sum_eq_zero]; intro m _; by_cases l:r<b.F.span (b.home i) (b.home m)
  · rw [h _ _ l,zero_mul]
  rw [g _ _ (by have hp := b.F.tri (b.home i) (b.home m) (b.home j); omega),mul_zero]
lemma FiniteOp.powr (h : FiniteOp b r A) (n : ℕ) : FiniteOp b (n*r) (A^n) := by
  induction n with
  | zero => simp only [pow_zero]; apply FiniteOp.oneOp
  | succ n ih => rw [pow_succ,add_mul,one_mul]; exact ih.times h

def cage (b : Stage Y I D G) (x : Y) (v : ℕ) (A : Op I) := strip b (bay b.F x v)*A*strip b (bay b.F x v)
lemma locker {X : Raw D I} (A : Op I) (o : Y) : ‖cage b o v A‖≤‖A‖ := by
  unfold cage; let S := strip b (bay b.F o v); have ht : ‖S‖ ≤ 1 := IsStarProjection.norm_le S (cutM_idp _)
  apply (norm_mul_le ..).trans; exact (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))) ht (norm_nonneg _) (by positivity)).trans (by simp)
lemma latched (A : Op I) (o : Y) (i j) : cage b o v A i j=if b.F.span o (b.home i) ≤ v ∧ b.F.span o (b.home j) ≤ v then A i j else 0 := by
  rw [cage,stripR,stripL]; by_cases g:b.F.span o (b.home i)≤v <;> by_cases l:b.F.span o (b.home j)≤v <;> simp [g,l]
lemma lock_tight (h : FiniteOp b k A) (o : Y) (n : ℕ) (i j : I) (p : b.F.span o (b.home i)+n*k≤v) :
    (cage b o v A ^ n) i j = (A^n) i j := by
  induction n generalizing i with
  | zero => rw [pow_zero,pow_zero]
  | succ n ih =>
    rw [pow_succ',pow_succ' A, Matrix.mul_apply, Matrix.mul_apply]
    apply sum_congr rfl; intro x _; have hx := b.F.tri o (b.home i) (b.home x); rw [add_mul,one_mul] at p
    rw [latched]; by_cases e : k<b.F.span (b.home i) (b.home x)
    · rw [h i x e]; simp
    rw [if_pos (by constructor <;> omega), ih x (by omega)]
variable (N : Seal Y→Raw D I) (W : Seal Y→Toll I)
lemma cage_lip (h : ∀ S, Ticket s t S (W S) (N S)) (p : Ledger a W K) (he : 0 ≤ a) (o : Y) (x y : D) (r k : ℕ) :
    ‖cage b o r (lop N k x)-cage b o r (lop N k y)‖ ≤ K*b.eval (bay b.F o (r+k)) x y := by
  let T := bay b.F o (r+k); let d := b.eval T x y; let H := saleM a W
  have hd : 0≤d := b.pos ..
  let C : Op I := cage b o r (lop N k x)-cage b o r (lop N k y)
  refine schur (fun i j=> H i j*d) C (K*d) (mul_nonneg p.posP hd) (fun i j=>?_) (fun i=>?_) (fun i=>?_)
  · unfold C; rw [Matrix.sub_apply,latched,latched]; split_ifs with g
    · rw [lop,lop,Matrix.sum_apply, Matrix.sum_apply,←sum_sub_distrib]; apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ S∈ch Y k,(rent a S*W S i j)*d := by
          apply sum_le_sum; intro S hs; have hk := (h S).expo i j
          by_cases H : W S i j=0
          · apply (hk.variation x y).trans; simp [H]
          obtain ⟨l,w,_⟩ := hk.triggered H
          have hg : S⊆T := by
            intro x hx; rw [show T=bay b.F o (r+k) from rfl,bay_mem]; apply (b.F.tri o (b.home i) x).trans; apply Nat.add_le_add g.1
            exact ((l.lim _ w _ hx).trans (mem_filter.mp hs).2).le
          exact (hk.variation x y).trans (mul_le_mul (le_mul_of_one_le_left hk.positive (rent_one he _)) (b.includeV hg x y) (b.pos ..) (mul_nonneg (rent_pos ..).le hk.positive))
        _ ≤ _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun S _ _=>mul_nonneg (rent_pos ..).le ((h S).nonn _ _))) hd
    rw [sub_self,norm_zero]; exact mul_nonneg (sale_nn (fun S=>(h S).nonn) a _ _) hd
  · rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (p.rows i) hd
  rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (p.cols i) hd
lemma RootedK.tiesK {A : Raw D I} (h : RootedK s t a K A) : Inter s t A := by
  obtain ⟨F,C,p,l,q⟩ := h; intro i x; rw [q,q,sum_mul,mul_sum]; exact sum_congr rfl fun l _=> (p l).frame i x
variable [Nonempty I]
def blockCost (q K : ℝ) (n : ℕ) := q^n + n*q^(n-1)*K
lemma lower_block (h : ∀ S, Ticket s s S (W S) (N S)) (p : Ledger a W K) (q : Capacity b C) (e : 0≤C) (u : ℝ) (he : 0≤u) (hk : 0≤a) (v n : ℕ) (d : ℝ) (hd : 0≤d) (B : ∀ x, ‖lop N v x‖ ≤ u) : let m := n*v+v; let V := C*((m:ℝ)+1)^4;
    RootedK s s d (V*Real.exp (d*V)*blockCost u K n) (fun x => lop N v x^n) := by
  intro m V; let R := blockCost u K n
  have hl x : FiniteOp b v (lop N v x) := lop_rad N W h x
  have hn := (lop_root (v:=v) N W h p).powers hk n
  let A := fun x=> lop N v x^n; have ht : Continuous A := by
    apply Continuous.pow
    exact continuous_finsetSum _ fun i _=> (h i).cont
  have hg := p.posP; refine row_earn q e hd hn.tiesK ht (show 0 ≤ R by unfold R blockCost; positivity) _ (fun x=> ((hl x).powr _).weak (by unfold m; omega)) ?_ ?_
  · intro i j x; change ‖(lop N v x ^ n) i j‖≤_; unfold R blockCost; exact (norm_entry ..).trans ((norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) (B x) _).trans (le_add_of_nonneg_right (by positivity))))
  intro i j x y; let X z := cage b (b.home i) (n*v) (lop N v z)
  change ‖(A x) i j-(A y) i j‖≤_
  have hQ z : ‖X z‖ ≤ u := (locker (X:=A) ..).trans (B z) -- remove extra arg
  have hw z : A z i j=(X z ^ n) i j := (lock_tight (hl z) (b.home i) n i j (by simp [b.F.reflex])).symm
  have H : ‖X x-X y‖≤K*b.eval (bay b.F (b.home i) m) x y := cage_lip N W h p hk _ _ _ (n*v) v
  rw [hw x,hw y]; apply (norm_entry (X x^n-X y^n) i j).trans; apply (pow_near he (hQ _) (hQ _) n).trans
  unfold R blockCost; apply (mul_le_mul_of_nonneg_left H (by positivity)).trans; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (b.pos ..)
end YM.CF.Branch
