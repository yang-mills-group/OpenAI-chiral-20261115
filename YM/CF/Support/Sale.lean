import YM.CF.Support.Toll
set_option linter.unusedSectionVars false

/-! Support fees: row and column forms, same displayed expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
open Finset Function Fock
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]

abbrev Seal (Y : Type*) := Finset Y

def rent {Y : Type*} (a : ℝ) (S : Seal Y) := Real.exp (a*S.card)
lemma rent_pos (a : ℝ) (S : Seal Y) : 0<rent a S := Real.exp_pos _
lemma rent_one {a : ℝ} (h : 0 ≤ a) (S : Seal Y) : 1 ≤ rent a S := Real.one_le_exp (mul_nonneg h (by positivity)) -- tune
lemma rent_join (S T : Seal Y) {a : ℝ} (h : 0 ≤ a) : rent a (S∪T)≤rent a S*rent a T := by
  unfold rent; rw [←Real.exp_add,←mul_add]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ h; exact_mod_cast (card_union_le S T)
lemma rent_up {a k : ℝ} (h : a≤k) (S : Seal Y) : rent a S≤rent k S := Real.exp_monotone (mul_le_mul_of_nonneg_right h (by positivity))

structure Ticket {b : Stage Y I D G} (s t : Tag b) (S : Seal Y) (c : Toll I) (A : Raw D I) : Prop where
  frame : Inter s t A
  expo (i j : I) : Expo b S i j (c i j) (fun x=> A x i j)

def saleM (a : ℝ) (w : Seal Y→Toll I) (i j) := ∑ S, rent a S*w S i j
structure Ledger (a : ℝ) (w : Seal Y→Toll I) (K : ℝ) : Prop where
  posP : 0 ≤ K
  rows i : ∑ j, saleM a w i j≤K
  cols i : ∑ j, saleM a w j i≤K

def RootedK {b : Stage Y I D G} (s t : Tag b) (a : ℝ) (w : ℝ) (A : Raw D I) : Prop :=
  ∃ (F : Seal Y→ Raw D I) (C : Seal Y→ Toll I), (∀ S, Ticket s t S (C S) (F S)) ∧ Ledger a C w ∧ ∀ x, A x=∑ S, F S x
variable {b : Stage Y I D G} {s t : Tag b} {S T : Seal Y} {f g : Raw D I} {r a d m K : ℝ} {c u : Toll I}
namespace Ticket
lemma nonn (h : Ticket s t S c f) (i j) : 0 ≤ c i j := (h.expo i j).positive
lemma cont (h : Ticket s t S c f) : Continuous f := continuous_matrix fun i j=>(h.expo i j).connected
lemma addT (h : Ticket s t S c f) (g' : Ticket s t S u g) : Ticket s t S (c+u) (fun x=>f x+g x) :=
  ⟨fun i x=> by rw [mul_add,add_mul,h.frame i x,g'.frame i x], fun i j=>(h.expo i j).add (g'.expo i j)⟩
lemma scale (h : Ticket s t S c f) (r : ℂ) : Ticket s t S (fun i j=>‖r‖*c i j) (fun x=> r • f x) := by
  refine ⟨fun i x=>?_,fun i j=> (h.expo i j).discount r⟩
  rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,h.frame i x]
lemma starT (h : Ticket s t S c f) : Ticket t s S (Function.swap c) (fun x=> star (f x)) := by
  refine ⟨fun i x=>?_, fun i j=> (h.expo j i).dual.swap'⟩
  rw [h.frame.frame,star_mul,star_mul,star_star,mul_assoc,mul_assoc,show star _ * (s.run i).val=1 from (s.run i).property.1,mul_one]
lemma ccT (h : Ticket s t S c f) : Ticket s.reverseV t.reverseV S c (fun x=> cc (f x)) := by
  refine ⟨fun i x=>?_,fun i j=> (h.expo i j).dual⟩
  change cc _ * cc _=cc _*cc _; rw [←cc_mul,←cc_mul,h.frame i x]
lemma zeroT (S) : Ticket s t S 0 (fun _=>0) := ⟨fun i x=> by simp,fun i j=> nothing ..⟩
lemma sumT {J : Type*} (t₁ : Finset J) (c : J→Toll I) (f : J→Raw D I) (h : ∀ i∈t₁, Ticket s t S (c i) (f i)) :
    Ticket s t S (fun i j=>∑ k∈t₁,c k i j) (fun x=> ∑ k∈t₁,f k x) := by
  refine ⟨fun i x=>?_,fun i j=>?_⟩
  · rw [sum_mul,mul_sum]; exact sum_congr rfl fun a ha=> (h a ha).frame i x
  simp_rw [Matrix.sum_apply]; exact Expo.sumK t₁ (fun k=>c k i j) (fun k x=> f k x i j) (fun k hk=>(h k hk).expo i j)
end Ticket
variable {w : Seal Y→Toll I}
lemma sale_mono {w' : Seal Y→Toll I} (h : ∀ S i j, rent a S*w S i j ≤ rent d S*w' S i j) : ∀ i j, saleM a w i j≤saleM d w' i j := fun i j=> sum_le_sum (fun x _=> h x i j)
lemma sale_nn (h : ∀ S i j,0 ≤ w S i j) (a : ℝ) : ∀ i j, 0 ≤ saleM a w i j := fun i j=> sum_nonneg (fun S _=>mul_nonneg (rent_pos a S).le (h S i j))
namespace Ledger
lemma basic (L : Ledger a w r) (p : ∀ S i j, 0 ≤ w S i j) (S i j) : rent a S * w S i j ≤ r := by
  calc
    _ ≤ saleM a w i j := single_le_sum (f:=fun S'=> rent a S'*w S' i j) (fun S _=>mul_nonneg (rent_pos a S).le (p S i j)) (mem_univ S)
    _ ≤ _ := (single_le_sum (fun j₁ (_ : j₁∈(univ:Finset I))=>sale_nn p a i j₁) (mem_univ j)).trans (L.rows i)
lemma price (L : Ledger a w r) (ha : 0≤a) (p : ∀ S i j, 0 ≤ w S i j) (S i j) : w S i j ≤ r := by
  exact (le_mul_of_one_le_left (p S i j) (rent_one ha S)).trans (L.basic p S i j)
lemma book (L : Ledger a w r) (h : r≤m) : Ledger a w m := ⟨L.posP.trans h,fun x=>(L.rows x).trans h,fun x=>(L.cols x).trans h⟩
lemma lowers (L : Ledger a w r) {w'} (v : ∀ S i j, rent d S*w' S i j ≤ rent a S*w S i j) : Ledger d w' r := ⟨L.posP,
  fun i=>(sum_le_sum (fun j _=>sale_mono v i j)).trans (L.rows i), fun i=>(sum_le_sum fun j _=>sale_mono v j i).trans (L.cols i)⟩
lemma pairT {w' : Seal Y→Toll I} (L : Ledger a w r) (h : Ledger a w' d) : Ledger a (w+w') (r+d) := by
  have hp i j : saleM a (w+w') i j=saleM a w i j+saleM a w' i j := by simp only [saleM, Pi.add_apply, mul_add,sum_add_distrib]
  refine ⟨add_nonneg L.posP h.posP,fun i=>?_,fun i=>?_⟩ <;> simp_rw [hp,sum_add_distrib]
  · exact add_le_add (L.rows i) (h.rows i)
  exact add_le_add (L.cols i) (h.cols i)
lemma funds (L : Ledger a w r) (h : 0≤d) : Ledger a (fun S i j=>d*w S i j) (d*r) := by
  have he i j : saleM a (fun S i j=>d*w S i j) i j=d*saleM a w i j := by
    simp only [saleM,mul_sum]; exact sum_congr rfl (fun i _=>by ring)
  refine ⟨mul_nonneg h L.posP,fun i=>?_,fun i=>?_⟩ <;> simp_rw [he, ←mul_sum]
  · exact mul_le_mul_of_nonneg_left (L.rows i) h
  exact mul_le_mul_of_nonneg_left (L.cols i) h
lemma flip (L : Ledger a w r) : Ledger a (fun S=>Function.swap (w S)) r := ⟨L.posP,L.cols,L.rows⟩
end Ledger
namespace RootedK
lemma drop (h : RootedK s t a r f) (e : d ≤ a) : RootedK s t d r f := by
  obtain ⟨F,C,p,j,q⟩ := h
  exact ⟨F,C,p,j.lowers (fun S i j=>mul_le_mul_of_nonneg_right (rent_up e S) ((p S).nonn i j)),q⟩
lemma books (h : RootedK s t a r f) (e : r≤K) : RootedK s t a K f := by obtain ⟨F,C,p,j,q⟩ := h; exact ⟨F,C,p,j.book e,q⟩
lemma raise (h : RootedK s t a r f) (d : ℂ) : RootedK s t a (‖d‖*r) (fun x=>d • f x) := by
  obtain ⟨F,C,p,j,q⟩ := h
  exact ⟨_,_,fun S=>(p S).scale d,j.funds (norm_nonneg d),fun x=> by dsimp only; rw [q, smul_sum]⟩
lemma minus (h : RootedK s t a r f) : RootedK s t a r (fun x=> -f x) := by simpa using h.raise (-1)
lemma plus (h : RootedK s t a r f) (k : RootedK s t a d g) : RootedK s t a (r+d) (fun x=>f x+g x) := by
  obtain ⟨F,C,p,j,q⟩ := h; obtain ⟨A,X,t,u,v⟩ := k
  exact ⟨_,C+X,fun S=>(p S).addT (t S),j.pairT u,fun x=> by dsimp only; rw [q,v,sum_add_distrib]⟩
lemma sub (h : RootedK s t a r f) (k : RootedK s t a d g) : RootedK s t a (r+d) (fun x=>f x-g x) := by simp_rw [sub_eq_add_neg]; exact h.plus k.minus
lemma ccUp (h : RootedK s t a r f) : RootedK s.reverseV t.reverseV a r (fun x=> cc (f x)) := by
  obtain ⟨F,C,p,j,q⟩ := h
  refine ⟨_,_,fun S=>(p S).ccT,j,fun x=>?_⟩; dsimp only; rw [q]; ext i j; simp [Matrix.sum_apply]
lemma starUp (h : RootedK s t a r f) : RootedK t s a r (fun x=>star (f x)) := by
  obtain ⟨F,C,p,j,q⟩ := h; exact ⟨_,_,fun S=>(p S).starT,j.flip,fun x=> by dsimp only; rw [q,star_sum]⟩
lemma free : RootedK s t a 0 (fun _=>0) := by
  refine ⟨_,_,fun S=>Ticket.zeroT S,⟨le_rfl,fun i=>?_,fun i=>?_⟩,fun i=>?_⟩ <;> simp [saleM]
lemma boundOp (h : RootedK s t a r f) (g : 0 ≤ a) (x) : ‖f x‖≤r := by
  obtain ⟨F,C,p,j,q⟩ := h
  refine schur (saleM a C) (f x) r j.posP ?_ j.rows j.cols
  intro i v; rw [q, Matrix.sum_apply]; apply (norm_sum_le ..).trans; exact sum_le_sum (fun S _=> ((p S).expo i v |>.bounded x).trans (le_mul_of_one_le_left ((p S).nonn i v) (rent_one g S)))
end RootedK
end YM.CF.Branch
