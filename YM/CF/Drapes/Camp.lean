import YM.CF.Support.Fleet
import Mathlib.Analysis.Complex.LocallyUniformLimit
/-! Credits including cylinder holomorphy on open sets. Stage money in these applications can later shrink. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Branch Filter
attribute [local instance] opCStarAlgebra
/-- smooth-use extensibility on same open domain, modelled with uniform limits -/
structure License (D:Type*) where
  valid: (D→ℂ)→ Prop
  plus {f g}: valid f → valid g→valid (f+g)
  mul {f g}: valid f→valid g→ valid (f*g)
  con (x:ℂ): valid (fun _=>x)
  sumK (f:ℕ→D→ℂ)(c:ℕ→ℝ): Summable c→(∀ i,valid (f i))→(∀ i d,‖f i d‖≤c i)→valid (fun x=>∑' i,f i x)
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
abbrev License.all (H: License D) (A:Raw D I):=∀ i j,H.valid fun x=> A x i j
lemma License.base (H:License D)(M:Op I): H.all (fun _=> M):=fun i j=> H.con _
lemma License.add {f g:Raw D I}(H: License D)(h:H.all f)(l:H.all g): H.all (f+g):=fun i j=> H.plus (h i j) (l i j)
lemma License.suppose {ι:Type*}(H:License D)(S:Finset ι)(f:ι→Raw D I)(h:∀ i∈S,H.all (f i)): H.all (fun x=>∑ i∈S,f i x):=by
  classical
  induction S using Finset.induction_on with
  | empty=> simpa only [sum_empty] using H.base (0:Op I)
  | @insert i S e ih=>
    have ht:= ih (fun b g=> h b (Finset.mem_insert_of_mem g))
    simp_rw [sum_insert e]; exact H.add (h i (Finset.mem_insert_self ..)) ht
lemma License.times {f g:Raw D I}(H:License D)(h:H.all f)(l:H.all g): H.all (fun x=>f x*g x):=by
  intro i j; simp only [Matrix.mul_apply]
  have he(S:Finset I): H.valid (fun x=>∑ k∈S,f x i k*g x k j):=by
    induction S using Finset.induction_on with
    | empty=> simp only [sum_empty]; exact H.con _
    | @insert k S e ih=> simp only [sum_insert e]; exact H.plus (H.mul (h i k) (l k j)) ih
  exact he _
variable {b : Stage Y I D G} {s t u : Tag b} {A B C : Raw D I} {V : ℝ} {L : License D}
structure Suite (L: License D)(s t : Tag b)(S:Seal Y)(c:Toll I)(A:Raw D I):Prop extends Ticket s t S c A where
  fuel : L.all A
def Crown (L:License D)(s t : Tag b)(a r:ℝ)(A:Raw D I) := ∃ (N:Seal Y→Raw D I)(C:Seal Y→Toll I), (∀ S,Suite L s t S (C S) (N S))∧ Ledger a C r∧ ∀ x,A x=∑ S,N S x
variable {S T : Seal Y}{c d : Toll I} {a r m q : ℝ} {M : Seal Y→ Toll I} {N:Seal Y→Raw D I}
lemma Suite.accel (p:Suite L s t S c A)(k:ℂ): Suite L s t S (fun i j=>‖k‖*c i j) (fun x=>k • A x):= ⟨p.toTicket.scale k,fun i j=> L.mul (L.con k) (p.fuel i j)⟩
lemma Suite.free (S:Seal Y) : Suite L s t S 0 (fun _=>0):= ⟨Ticket.zeroT S, L.base _⟩
lemma Suite.jointK (p:Suite L s t S c A)(f:Suite L t u T d B): Suite L s u (S∪T) (charge c d) (fun x=> A x*B x):=⟨p.toTicket.joinT f.toTicket,L.times p.fuel f.fuel⟩
lemma Suite.plus (p:Suite L s t S c A)(f:Suite L s t S d B): Suite L s t S (c+d) (fun x=> A x+B x):= ⟨p.toTicket.addT f.toTicket, L.add p.fuel f.fuel⟩
namespace Crown
lemma lib (h:Crown L s t a r A): RootedK s t a r A:=by obtain ⟨N,C,e,f,g⟩:=h; exact ⟨N,C,fun S=> (e S).toTicket,f,g⟩
lemma air (h:Crown L s t a r A): L.all A:=by obtain ⟨N,C,e,f,g⟩:=h; rw [funext g]; exact L.suppose _ N (fun i _=> (e i).fuel)
lemma free : Crown L s t a 0 (fun _=>0) := by
  refine ⟨_,_,fun S=>Suite.free S,⟨le_rfl,fun i=>?_,fun i=>?_⟩,fun i=>?_⟩ <;> simp [saleM]
lemma drop (h:Crown L s t a r A) (e:m≤a) : Crown L s t m r A := by
  obtain ⟨F,C,p,j,q⟩:=h
  exact ⟨F,C,p,j.lowers (fun S i v=>mul_le_mul_of_nonneg_right (rent_up e S) ((p S).nonn i v)),q⟩
lemma books (h:Crown L s t a r A)(e:r≤m) : Crown L s t a m A :=by obtain ⟨F,C,l,p,q⟩:=h; exact ⟨F,C,l,p.book e,q⟩
lemma scale (h:Crown L s t a r A)(k:ℂ) : Crown L s t a (‖k‖*r) (fun x=> k • A x):=by
  obtain ⟨F,C,l,p,q⟩:=h; exact ⟨_,_,fun S=>(l S).accel k,p.funds (norm_nonneg _),fun x=> by dsimp only; rw [q,Finset.smul_sum]⟩
lemma minus (h:Crown L s t a r A): Crown L s t a r (fun x=> -A x):=by simpa using h.scale (-1)
lemma plus (h:Crown L s t a r A)(e:Crown L s t a m B) : Crown L s t a (r+m) (fun x=> A x+B x):=by
  obtain ⟨F,C,p,j,q⟩:=h; obtain ⟨N,R,t,u,v⟩:=e
  exact ⟨_,_,fun S=>(p S).plus (t S),j.pairT u,fun x=> by dsimp only; rw [q,v,sum_add_distrib]⟩
lemma sub (h:Crown L s t a r A)(g:Crown L s t a m B): Crown L s t a (r+m) (fun x=> A x-B x):=by simp_rw [sub_eq_add_neg]; exact h.plus g.minus
lemma absorb {J: Type*}[Fintype J] (W:J→Seal Y) (F:J→Raw D I)(C:J→Toll I)(a:ℝ)(hp:0≤q)(B:Raw D I)
    (H:∀ i, Suite L s t (W i) (C i) (F i))(k:∀ x,B x=∑ i:J,F i x)(e:∀ i:I,∑ j:I,∑ l:J,rent a (W l)*C l i j ≤ q)(g:∀ j:I,∑ i:I,∑ l:J,rent a (W l)*C l i j≤q) : Crown L s t a q B:=by
  let D' X i j:=∑ l∈dest W X, C l i j
  have he i j:saleM a D' i j=∑ l,rent a (W l)*C l i j:=by rw [lump W (fun l=>_)]; unfold saleM D'; apply sum_congr rfl; intro X _; rw [mul_sum]; refine sum_congr rfl fun i hi=>?_ ; rw [show W i=X from (mem_filter.mp hi).2]
  refine ⟨_,D',fun S=>⟨Ticket.sumT (dest W S) C F (fun i hi=>by rw [← show W i=S from (mem_filter.mp hi).2]; exact (H i).toTicket), L.suppose _ _ (fun i _=>(H i).fuel)⟩,⟨hp,?_,?_⟩,fun x=>by rw [k,lump W (fun i=> F i x)]⟩ <;> simp_rw [he]; exact e; exact g
lemma product (h:Crown L s t a r A)(g:Crown L t u a m B)(p:0≤a): Crown L s u a (2*(r*m)) (fun x=> A x*B x):=by
  obtain ⟨F,C,e,l,H⟩:=h; obtain ⟨V,N,w,t,H'⟩:=g
  let f (p:Seal Y×Seal Y)(x):= F p.1 x * V p.2 x
  have hx x: A x*B x=∑ i,f i x:=by rw [Fintype.sum_prod_type,H,H']; simp only [sum_mul,mul_sum]; rw [sum_comm]
  have hr:=l.posP; have hq:=t.posP
  exact absorb (fun (u:Seal Y×Seal Y)=>u.1∪u.2) f _ a (by positivity) _ (fun i=>(e i.1).jointK (w i.2)) hx (slope_row (fun i=>(e i).nonn) (fun i=>(w i).nonn) l t p) (slope_col (fun i=>(e i).nonn) (fun i=>(w i).nonn) l t p)
lemma ident (L:License D)(s:Tag b)(a:ℝ): Crown L s s a (Real.exp a) (fun _=>1) :=by
  -- repeat coloring
  let W (x:Y) := ({x}:Seal Y)
  let F (x:Y) : Raw D I := fun _=>strip b (W x)
  let C (x:Y) : Toll I := fun i j => if i=j ∧ b.home i=x then 1 else 0
  have Lx x : Ticket s s (W x) (C x) (F x) := by
    refine ⟨fun i z=> strip_tag s i _, fun i j=>?_⟩
    have hp d : F x d i j=(C x i j:ℂ) := by unfold F C; by_cases g:i=j <;> by_cases h:b.home i=x <;> simp_all [strip,cutM,board,W]
    by_cases g:i=j ∧ b.home i=x
    · have H : C x i j=1 := if_pos g
      refine ⟨by rw [H]; exact zero_le_one,fun _=>⟨.single x,by simp [W,g.2],by rw [←g.1]; simp [W,g.2]⟩,?_,?_,continuous_const⟩
      · intro d; rw [hp d,H,Complex.ofReal_one,norm_one]
      intro z t; rw [hp z, sub_self,norm_zero,H,one_mul]; exact b.pos ..
    have hc : C x i j=0 := if_neg g
    simp_rw [hp,hc,Complex.ofReal_zero]; exact nothing ..
  refine absorb W F C a (Real.exp_pos a).le _ (fun i=>⟨Lx i, L.base _⟩) ?_ ?_ ?_
  · intro v; ext i j; rw [Matrix.sum_apply]; by_cases g:i=j
    · subst j; simp only [F,strip,cutM,board,W,mem_filter,mem_univ,true_and,mem_singleton, Matrix.diagonal_apply_eq,Matrix.one_apply_eq]; simp
    simp [F,strip,cutM,g]
  · intro i; unfold C; simp only [ite_and,mul_ite,mul_one,mul_zero]; rw [sum_eq_single_of_mem _ (mem_univ i)]
    · simp [W,rent]
    intro j _ h; simp [Ne.symm h]
  intro i; unfold C; simp only [ite_and,mul_ite,mul_one,mul_zero]; rw [sum_eq_single_of_mem _ (mem_univ i)]; simp [W,rent]
  intro j _ h; simp [h]
lemma powers (h : Crown L s s a r A) (g : 0≤a) (n : ℕ) : Crown L s s a (Real.exp a*(2*r)^n) (fun x=> A x ^ n) := by
  induction n with
  | zero => simpa using ident L s a
  | succ n ih => rw [pow_succ,show Real.exp a*((2*r)^n*(2*r))=2*((Real.exp a*(2*r)^n)*r) by ring]; simp_rw [pow_succ (A _)]
                 exact ih.product h g
lemma sumK {J : Type*} (p : Finset J) (k : J→ℝ) (f : J→Raw D I) (h : ∀ i∈p, Crown L s t a (k i) (f i)) : Crown L s t a (∑ j∈p,k j) (fun x=>∑ j∈p,f j x) := by
  classical
  induction p using Finset.induction_on with
  | empty => simp only [sum_empty]; exact free
  | @insert i p e ih => simp only [sum_insert e]; exact (h i (mem_insert_self i p)).plus (ih (fun j hj=>h _ (mem_insert_of_mem hj)))

end Crown
end YM.CF.Drapes
