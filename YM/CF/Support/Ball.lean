import YM.CF.Support.Flow

/-! Row ball collection and support thinning. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {a d C K : ℝ}
structure Capacity (b : Stage Y I D G) (C : ℝ) : Prop where
  grove (x : Y) (j : ℕ) : Grove b.F (bay b.F x j)
  ball (x : Y) (j : ℕ) : ((bay b.F x j).card:ℝ)≤C*((j:ℝ)+1)^4
  place (x : Y) (j : ℕ) : ((board b (bay b.F x j)).card:ℝ)≤C*((j:ℝ)+1)^4

def FiniteOp (b : Stage Y I D G) (m : ℕ) (A : Op I) := ∀ i j, m < b.F.span (b.home i) (b.home j) → A i j=0
variable {F : Raw D I} {m M v : ℕ}
lemma stripe1 (b : Stage Y I D G) (x : Y) (i j : I) : strip b {x} i j=if b.home i=x ∧ i=j then 1 else 0 := by
  by_cases h:i=j
  · subst j; simp [strip,cutM,board]
  simp [strip,cutM,h]
lemma row_earn {a C : ℝ} (h : Capacity b C) (c : 0≤C) (p : 0 ≤ a) (f : Inter s t F) (e : Continuous F) (g : 0≤K) (m : ℕ)
    (L : ∀ x, FiniteOp b m (F x)) (A : ∀ i j x, ‖F x i j‖ ≤ K) (B : ∀ i j x y, ‖F x i j-F y i j‖≤ K * b.eval (bay b.F (b.home i) m) x y) :
    RootedK s t a (C*((m:ℝ)+1)^4 * Real.exp (a*(C*((m:ℝ)+1)^4))*K) F := by
  let S := fun i=>bay b.F i m; let D' := fun i (x:D)=> strip b ({i}:Seal Y)*F x
  let X (y:Y) (i j:I) := if y=b.home i ∧ b.home j∈S (b.home i) then K else 0
  have ht y : Ticket s t (S y) (X y) (D' y) := by
    refine ⟨fun i x=>?_,fun i j=>?_⟩
    · dsimp only [D']; rw [mul_assoc,f i,←mul_assoc,strip_tag,mul_assoc]
    have he d : D' y d i j=if y=b.home i then F d i j else 0 := by unfold D'; rw [stripL]; simp [eq_comm]
    simp_rw [he]; unfold X; by_cases l:y=b.home i
    · subst y; simp only [ite_true,true_and]; by_cases k:b.home j ∈ S (b.home i)
      · rw [if_pos k]; exact ⟨g,fun _=>⟨h.grove _ _,bay_mem m|>.mpr (by rw [b.F.reflex]; omega),k⟩,A i j,B i j,e.matrix_elem i j⟩
      rw [if_neg k]; simp_rw [show ∀ x, F x i j=0 from fun x=> L x i j (lt_of_not_ge fun ℓ=>k ((bay_mem _).mpr ℓ))]; exact nothing ..
    simp only [l,false_and,ite_false]; exact nothing ..
  let V := C*((m:ℝ)+1)^4; let R := Real.exp (a*V); let W := V*R*K; have hv : 0≤V := by unfold V; positivity
  have hr : 0<R := Real.exp_pos _
  have hE x : rent a (S x) ≤ R := Real.exp_monotone (mul_le_mul_of_nonneg_left (h.ball x m) p)
  have hx : ∀ x:D,F x=∑ i:Y,D' i x := by
    intro x; ext i j; rw [Matrix.sum_apply]; simp_rw [D',stripL, mem_singleton]; simp
  have hk i j : ∑ l,rent a (S l)*X l i j = rent a (S (b.home i))* (if b.home j∈S (b.home i) then K else 0) := by
    unfold X; simp only [ite_and,mul_ite,mul_zero]; simp -- tune
  refine lumped S D' X a (show 0≤W by unfold W; positivity) F ht hx ?_ ?_
  · intro i; simp_rw [hk]; -- requires unfold ticket in lemma
    simp_rw [mul_ite,mul_zero, ←sum_filter];
    unfold W; rw [sum_const,nsmul_eq_mul,mul_assoc]
    exact mul_le_mul (show ((board b (S (b.home i))).card:ℝ) ≤ V from h.place _ _) (mul_le_mul_of_nonneg_right (hE _) g) (mul_nonneg (rent_pos ..).le g) hv
  intro j; simp_rw [hk]; simp_rw [mul_ite, mul_zero,←sum_filter]
  unfold W; rw [mul_assoc]; apply le_trans (sum_le_sum (g:=fun _=>R*K) (fun i _=>mul_le_mul_of_nonneg_right (hE _) g))
  rw [sum_const,nsmul_eq_mul]
  have hp : univ.filter (fun i=>b.home j∈S (b.home i))=board b (S (b.home j)) := by ext i; simp [board,S,b.F.sym (b.home i)]
  rw [hp]; exact mul_le_mul_of_nonneg_right (h.place _ _) (mul_nonneg hr.le g)

variable (N : Seal Y → Raw D I) (U : Seal Y→Toll I)
-- truncated displays
abbrev ch (Y : Type*) [Fintype Y] (v : ℕ) := (univ : Finset (Seal Y)).filter fun i=>i.card < v
def lop (v : ℕ) (x : D) : Op I := ∑ S ∈ ch Y v,N S x

theorem lop_root (h : ∀ S, Ticket s t S (U S) (N S)) (g : Ledger a U K) : RootedK s t a K (lop N v) := by
  let X S := if S∈ch Y v then U S else 0
  let A S := if S∈ch Y v then N S else 0
  refine ⟨A,X,fun S=>?_,g.lowers ?_,?_⟩
  · by_cases e:S∈ch Y v <;> unfold A X <;> simp only [e,ite_true,ite_false]; exact h S; exact Ticket.zeroT S
  · intro S i j; by_cases e:S∈ch Y v
    · rw [show X S=U S from if_pos e]
    rw [show X S=0 from if_neg e]; exact mul_le_mul_of_nonneg_left ((h S).nonn i j) (rent_pos _ _).le
  intro x; rw [lop]; symm; rw [←sum_subset (ch Y v).subset_univ]; apply sum_congr rfl; intro i hi; rw [show A i=N i from if_pos hi]
  intro i _ g; rw [show A i=0 from if_neg g]; rfl -- indent
lemma lop_rad (h : ∀ S, Ticket s t S (U S) (N S)) (x : D) : FiniteOp b v (lop N v x) := by
  intro i j g
  unfold lop; rw [Matrix.sum_apply]; apply sum_eq_zero; intro S hs
  have he := (h S).expo i j; have hz := (mem_filter.mp hs).2
  have ht : U S i j=0 := by
    by_contra k; obtain ⟨p,x,y⟩ := he.triggered k; exact (lt_asymm g ((p.lim _ x _ y).trans hz))
  exact norm_le_zero_iff.mp ((he.bounded x).trans ht.le)
lemma lip_tail (h : ∀ S, Ticket s t S (U S) (N S)) (p : Ledger a U K) (w : ∀ x,F x=∑ S,N S x) (he : 0 ≤ a) :
    RootedK s t (a/2) (Real.exp (-a/2*v)*K) (fun x=> F x-lop N v x) := by
  let t' := Real.exp (-a/2*v); have Q := p.funds (Real.exp_pos (-a/2*v)).le
  let X S := if S∈(ch Y v)ᶜ then U S else 0
  let A S := if S∈(ch Y v)ᶜ then N S else 0
  refine ⟨A,X,fun S=>?_,Q.lowers ?_,?_⟩
  · unfold A X; by_cases e:S∈(ch Y v)ᶜ <;> simp only [e,ite_true,ite_false]; exact h S; exact Ticket.zeroT S
  · intro S i j; change _≤rent a S * (t'*U S i j); by_cases e:S∈(ch Y v)ᶜ
    · rw [show X S=U S from if_pos e,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ ((h S).nonn i j)
      have hp : v ≤ S.card := by simpa [ch] using e
      unfold rent t'; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; have hu : (v:ℝ)≤S.card := by exact_mod_cast hp
      nlinarith [mul_le_mul_of_nonneg_left hu he]
    rw [show X S=0 from if_neg e]; simp only [Pi.zero_apply, mul_zero]; exact mul_nonneg (rent_pos ..).le (mul_nonneg (Real.exp_pos _).le ((h S).nonn _ _))
  intro x; dsimp only; rw [w x,←sum_add_sum_compl (ch Y v),lop,add_sub_cancel_left]; symm; rw [←sum_subset ((ch Y v)ᶜ).subset_univ]; apply sum_congr rfl; intro i hi; rw [show A i=N i from if_pos hi]
  intro i _ g; rw [show A i=0 from if_neg g]; rfl
end YM.CF.Branch
