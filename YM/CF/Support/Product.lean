import YM.CF.Support.Sale

/-! Distinct supports and gauge covariance retained in products. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Branch
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
open Finset Function Fock
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t u : Tag b} {J : Type*} [Fintype J]

def dest (w : J → Seal Y) (X : Seal Y) := univ.filter fun i=> w i=X
lemma lump {N : Type*} [AddCommMonoid N] (w : J → Seal Y) (f : J→N) : ∑ i:J, f i=∑ X:Seal Y, ∑ i∈dest w X, f i := by
  simp only [dest,sum_filter]; rw [sum_comm]; simp
lemma lumped {Q : ℝ} (W : J→Seal Y) (F : J→Raw D I) (C : J → Toll I) (a : ℝ) (hp : 0≤Q) (B : Raw D I)
    (L : ∀ i, Ticket s t (W i) (C i) (F i)) (k : ∀ x,B x=∑ i:J,F i x)
    (e : ∀ i:I, ∑ j:I,∑ l:J,rent a (W l)*C l i j ≤ Q) (g : ∀ j:I,∑ i:I,∑ l:J,rent a (W l)*C l i j≤Q) :
    RootedK s t a Q B := by
  let D' X i j := ∑ l∈dest W X, C l i j
  have he i j : saleM a D' i j=∑ l,rent a (W l)*C l i j := by
    rw [lump W (fun l=>_)]; unfold saleM D'; apply sum_congr rfl; intro X _
    rw [mul_sum]; apply sum_congr rfl; intro i l; rw [show W i=X from (mem_filter.mp l).2]
  refine ⟨_,D',fun S=>Ticket.sumT (dest W S) C F (fun i hi=>by have hL:=L i; rw [show W i=S from (mem_filter.mp hi).2] at hL; exact hL),⟨hp,?_,?_⟩,fun x=>by rw [k,lump W (fun i=>F i x)]⟩ <;> simp_rw [he]
  · exact e
  exact g

variable {S T : Seal Y} {c p : Toll I} {A B : Raw D I} {r d k a : ℝ} {w q : Seal Y→Toll I}
def charge (c p : Toll I) (i k) := ∑ j,2*(c i j*p j k)
lemma Ticket.joinT (h : Ticket s t S c A) (g : Ticket t u T p B) : Ticket s u (S∪T) (charge c p) (fun x=>A x*B x) := by
  refine ⟨fun i x=>?_,fun i j=>?_⟩
  · rw [mul_assoc,g.frame, ←mul_assoc,h.frame,mul_assoc]
  simp only [Matrix.mul_apply]; exact Expo.sumK univ _ _ (fun l _=>(h.expo i l).fuse (g.expo l j))
lemma slope_row (h : ∀ S i j, 0 ≤ w S i j) (g : ∀ S i j, 0 ≤ q S i j) (hb : Ledger a w r) (hd : Ledger a q d) (p : 0≤a) (i : I) :
    ∑ j:I, ∑ l:Seal Y×Seal Y,rent a (l.1∪l.2)*charge (w l.1) (q l.2) i j ≤ 2*(r*d) := by
  let m i j k S T := rent a S*w S i j * (rent a T*q T j k)
  have he j k : ∑ S,∑ T, m i j k S T = saleM a w i j * saleM a q j k := by simp only [saleM,m,sum_mul,mul_sum]; rw [sum_comm]
  have hp (k:I) : (∑ l:Seal Y×Seal Y, rent a (l.1∪l.2)*charge (w l.1) (q l.2) i k) ≤ 2 * ∑ j:I,saleM a w i j*saleM a q j k := by
    rw [Fintype.sum_prod_type]; simp_rw [charge,mul_sum]
    rw [show ∑ x:I,(2:ℝ) * (saleM a w i x*saleM a q x k)= ∑ S:Seal Y,∑ T:Seal Y,∑ x:I,(2:ℝ)*m i x k S T by
      simp_rw [←he, mul_sum]; rw [sum_comm]; simp_rw [sum_comm (f:=fun (x:I) (b:Seal Y) => (2:ℝ)*m i x k _ b)]]
    apply sum_le_sum; intro S _; apply sum_le_sum; intro T _; apply sum_le_sum; intro v _
    apply le_trans (mul_le_mul_of_nonneg_right (rent_join S T p) (mul_nonneg (by norm_num) (mul_nonneg (h S i v) (g T v k))))
    unfold m; exact le_of_eq (by ring)
  apply (sum_le_sum (fun k (_:k∈(univ:Finset I)) => hp k)).trans
  rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [sum_comm]; simp_rw [←mul_sum]
  apply le_trans (sum_le_sum (g:=fun j=>saleM a w i j*d) (fun j _=>mul_le_mul_of_nonneg_left (hd.rows j) (sale_nn h a i j)))
  rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (hb.rows _) hd.posP
lemma slope_col (h : ∀ S i j, 0 ≤ w S i j) (g : ∀ S i j, 0 ≤ q S i j) (hb : Ledger a w r) (hd : Ledger a q d) (p : 0≤a) (i : I) :
    ∑ j:I, ∑ l:Seal Y×Seal Y,rent a (l.1∪l.2)*charge (w l.1) (q l.2) j i≤2*(r*d) := by
  rw [mul_comm r]
  have H := slope_row (w:=fun S=>Function.swap (q S)) (q:=fun S=>Function.swap (w S)) (fun S i j=>g S j i) (fun S i j=>h S j i) hd.flip hb.flip p i
  apply le_trans (le_of_eq _) H; apply sum_congr rfl; intro j _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_comm]; apply sum_congr rfl; intro S _; apply sum_congr rfl; intro T _; simp [union_comm,charge,Function.swap,mul_comm]
lemma RootedK.product (h : RootedK s t a r A) (g : RootedK t u a d B) (p : 0 ≤ a) : RootedK s u a (2*(r*d)) (fun x=>A x*B x) := by
  obtain ⟨F,C,e,l,H⟩ := h; obtain ⟨V,N,w,t,H'⟩ := g
  let f (p : Seal Y×Seal Y) (x) := F p.1 x * V p.2 x
  have hx x : A x*B x=∑ i,f i x := by rw [Fintype.sum_prod_type,H,H']; simp only [sum_mul,mul_sum]; rw [sum_comm]
  have hr := l.posP; have hq := t.posP
  exact lumped (fun (u:Seal Y×Seal Y)=>u.1∪u.2) f _ a (by positivity) _ (fun i=>(e i.1).joinT (w i.2)) hx (slope_row (fun i=>(e i).nonn) (fun i=>(w i).nonn) l t p) (slope_col (fun i=>(e i).nonn) (fun i=>(w i).nonn) l t p)
end YM.CF.Branch
