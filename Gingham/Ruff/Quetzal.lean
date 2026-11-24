import YM.CF.Drapes.Camp
/-! Crown with support stamp retained. Based on Crown algebra in Drapes/Camp. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Branch Drapes Filter
attribute [local instance] opCStarAlgebra

variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t u : Tag b} {A B C : Raw D I} {L : License D}
def Brooch (R: Seal Y→Prop)(L:License D)(s t:Tag b)(a r:ℝ)(A:Raw D I):Prop :=
  ∃ (N:Seal Y→Raw D I)(C:Seal Y→Toll I),
   (∀ S, Suite L s t S (C S) (N S))∧ Ledger a C r ∧ (∀ x,A x=∑ S,N S x) ∧
   ∀ S i j,C S i j≠0→ R S


namespace Brooch
variable {R R' R₁: Seal Y→Prop} {a r m q : ℝ}
lemma crown (p:Brooch R L s t a r A):Crown L s t a r A :=
  let ⟨n,c,p,f,e,_⟩:=p; ⟨n,c,p,f,e⟩
lemma positive (p:Brooch R L s t a r A):0 ≤ r :=
  let ⟨_,_,_,f,_⟩:=p; f.posP

lemma shape (p:Brooch R L s t a r A)
    (h:∀ S i j,Grove b.F S → b.home i∈S → b.home j∈S → R S → R' S):
    Brooch R' L s t a r A := by
  obtain ⟨N,c,p,f,e,g⟩:=p; refine ⟨N,c,p,f,e,fun S i j u=>?_⟩
  obtain ⟨x,v,w⟩:=((p S).expo i j).triggered u
  exact h S i j x v w (g S i j u)
lemma drop (p:Brooch R L s t a r A)(l:q≤a): Brooch R L s t q r A :=
  let ⟨N,c,p,f,e,g⟩:=p
  ⟨N,c,p,f.lowers (fun S i j=>mul_le_mul_of_nonneg_right (rent_up l S) ((p S).nonn i j)),e,g⟩
lemma books (p:Brooch R L s t a r A)(l:r≤q): Brooch R L s t a q A :=
  let ⟨N,c,p,f,e,g⟩:=p; ⟨N,c,p,f.book l,e,g⟩
lemma scale (p:Brooch R L s t a r A)(k:ℂ): Brooch R L s t a (‖k‖*r) (fun x=> k • A x):=by
  obtain ⟨F,C,l,p,q,g⟩:=p
  exact ⟨_,_,fun S=>(l S).accel k,p.funds (norm_nonneg k),fun x=> by dsimp only; rw [q,Finset.smul_sum],
          fun S i j h=> g S i j (right_ne_zero_of_mul h)⟩

lemma minus (h:Brooch R L s t a r A): Brooch R L s t a r (fun x=>-A x):=by simpa using h.scale (-1)
lemma plus (h:Brooch R L s t a r A)(e:Brooch R L s t a m B): Brooch R L s t a (r+m) (fun x=> A x+B x):=by
  obtain ⟨F,C,p,j,q,tt⟩:=h; obtain ⟨N,R0,t,u,v,vv⟩:=e
  refine ⟨_,_,fun S=>(p S).plus (t S),j.pairT u,fun x=> by dsimp only; rw [q,v,sum_add_distrib], fun S i j h=>?_⟩
  by_cases l: C S i j=0
  · apply vv S i j; change C S i j+ _≠0 at h; rwa [l,zero_add] at h
  exact tt S i j l

lemma sub (h:Brooch R L s t a r A)(g:Brooch R L s t a m B): Brooch R L s t a (r+m) (fun x=> A x-B x):=
  by simp_rw [sub_eq_add_neg]; exact h.plus g.minus

lemma free : Brooch R L s t a 0 (fun _=>0):=by
  refine ⟨_,_,fun S=>Suite.free S,⟨le_rfl,fun i=>?_,fun i=>?_⟩,fun i=>?_,?_⟩ <;>simp [saleM]
lemma sumK {J : Type*} (p : Finset J) (k : J→ℝ) (f : J→Raw D I) (h : ∀ i∈p, Brooch R L s t a (k i) (f i)) : Brooch R L s t a (∑ j∈p,k j) (fun x=>∑ j∈p,f j x) := by
  classical
  induction p using Finset.induction_on with
  | empty => simp only [sum_empty]; exact free
  | @insert i p e ih => simp only [sum_insert e]; exact (h i (mem_insert_self i p)).plus (ih (fun j hj=>h _ (mem_insert_of_mem hj)))
lemma absorb {J: Type*}[Fintype J] (W:J→Seal Y) (F:J→Raw D I)(C:J→Toll I)(a:ℝ)(hp:0≤q)(B:Raw D I)
    (H:∀ i, Suite L s t (W i) (C i) (F i))(k:∀ x,B x=∑ i:J,F i x)(e:∀ i:I,∑ j:I,∑ l:J,rent a (W l)*C l i j ≤ q)(g:∀ j:I,∑ i:I,∑ l:J,rent a (W l)*C l i j≤q) 
    (pkt : ∀ j u v,C j u v≠0 → R (W j)): Brooch R L s t a q B:=by
  let D' X i j:=∑ l∈dest W X, C l i j
  have he i j:saleM a D' i j=∑ l,rent a (W l)*C l i j:=by rw [lump W (fun l=>_)]; unfold saleM D'; apply sum_congr rfl; intro X _; rw [mul_sum]; refine sum_congr rfl fun i hi=>?_ ; rw [show W i=X from (mem_filter.mp hi).2]
  refine ⟨_,D',fun S=>⟨Ticket.sumT (dest W S) C F (fun i hi=>by rw [← show W i=S from (mem_filter.mp hi).2]; exact (H i).toTicket), L.suppose _ _ (fun i _=>(H i).fuel)⟩,⟨hp,?_,?_⟩,fun x=>by rw [k,lump W (fun i=> F i x)],?_⟩
  · simp_rw [he]; exact e
  · simp_rw [he]; exact g
  intro S i j n
  obtain ⟨l,h,t⟩:= exists_ne_zero_of_sum_ne_zero n
  exact (mem_filter.mp h).2 ▸ pkt l i j t


lemma product (h:Brooch R L s t a r A)(g:Crown L t u a m B)(p:0≤a)
  (z:∀ S T, R S → R (S∪T)): Brooch R L s u a (2*(r*m)) (fun x=> A x*B x):=by
  obtain ⟨F,C,e,l,H,hh⟩:=h; obtain ⟨V,N,w,t,H'⟩:=g
  let f (p:Seal Y×Seal Y)(x):= F p.1 x * V p.2 x
  have hx x: A x*B x=∑ i,f i x:=by rw [Fintype.sum_prod_type,H,H']; simp only [sum_mul,mul_sum]; rw [sum_comm]
  have hr:=l.posP; have hq:=t.posP
  refine absorb (fun (u:Seal Y×Seal Y)=>u.1∪u.2) f _ a (by positivity) _ (fun i=>(e i.1).jointK (w i.2)) hx (slope_row (fun i=>(e i).nonn) (fun i=>(w i).nonn) l t p) (slope_col (fun i=>(e i).nonn) (fun i=>(w i).nonn) l t p) ?_
  rintro ⟨b,x⟩ i j nz
  apply z
  change charge _ _ i j≠0 at nz
  obtain ⟨k,h,t0⟩:= exists_ne_zero_of_sum_ne_zero nz
  exact hh b i k (left_ne_zero_of_mul (right_ne_zero_of_mul t0))


lemma crowned (p:Crown L s t a r A): Brooch (fun _=>True) L s t a r A :=
 let ⟨n,d,f,g,t⟩:=p
 ⟨n,d,f,g,t,fun _ _ _ _=>True.intro⟩

