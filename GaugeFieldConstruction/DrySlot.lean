import GaugeFieldConstruction.Axe
import YM.CF.Moire.Niche
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Finset Function Fock Branch Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G}{L:License D}{q:ℝ}{s t : Tag b}
-- Crown variant retained at any marked flat argument
def DrySlot (L:License D)(s t : Tag b)(a r:ℝ)(A:Raw D I)(p:D→Prop) := ∃ (N:Seal Y→Raw D I)(C:Seal Y→Toll I), (∀ S,Suite L s t S (C S) (N S))∧ Ledger a C r∧ (∀ x,A x=∑ S,N S x)∧∀ S x,p x→ N S x=0
lemma DrySlot_absorb {J: Type*}[Fintype J] (W:J→Seal Y) (F:J→Raw D I)(C:J→Toll I)(a:ℝ)(hp:0≤q)(B:Raw D I)
    (H:∀ i, Suite L s t (W i) (C i) (F i))(k:∀ x,B x=∑ i:J,F i x)(e:∀ i:I,∑ j:I,∑ l:J,rent a (W l)*C l i j ≤ q)(g:∀ j:I,∑ i:I,∑ l:J,rent a (W l)*C l i j≤q) (p:D→Prop) (v:∀ i x,p x→ F i x=0) : DrySlot L s t a q B p:=by
  let D' X i j:=∑ l∈dest W X, C l i j
  have he i j:saleM a D' i j=∑ l,rent a (W l)*C l i j:=by rw [lump W (fun l=>_)]; unfold saleM D'; apply sum_congr rfl; intro X _; rw [mul_sum]; refine sum_congr rfl fun i hi=>?_ ; rw [show W i=X from (mem_filter.mp hi).2]
  refine ⟨_,D',fun S=>⟨Ticket.sumT (dest W S) C F (fun i hi=>by rw [← show W i=S from (mem_filter.mp hi).2]; exact (H i).toTicket), L.suppose _ _ (fun i _=>(H i).fuel)⟩,⟨hp,?_,?_⟩,fun x=>by rw [k,lump W (fun i=> F i x)],?_⟩
  · simp_rw [he]; exact e
  · simp_rw [he]; exact g
  intro X x h; exact sum_eq_zero fun i _=>v i x h
namespace DrySlot
variable {a d k:ℝ}{A B:Raw D I}{p:D→Prop}
lemma plus (h:DrySlot L s t a q A p)(r:DrySlot L s t a d B p):DrySlot L s t a (q+d) (fun x=>A x+B x) p:=by
 obtain ⟨F,C,g,n,h0,e⟩:=h
 obtain ⟨P,T,u,l,t,y⟩:=r
 refine ⟨_,_,fun i=>(g i).plus (u i),n.pairT l,fun x=>?_,?_⟩
 · try dsimp only; rw [h0,t,sum_add_distrib]
 intro S x v; change F S x + P S x=0; rw[e S x v,y S x v,add_zero]
lemma scale (h:DrySlot L s t a q A p)(c:ℂ):DrySlot L s t a (‖c‖*q) (fun x=>c • A x) p:=by
 obtain ⟨F,C,m,u,y,l⟩:=h; exact ⟨_,_,fun i=>(m i).accel c,u.funds (norm_nonneg _),fun x=> by try dsimp only; rw [y,Finset.smul_sum],fun S x v=>by rw [l S x v,smul_zero]⟩
lemma neg (h:DrySlot L s t a q A p):DrySlot L s t a q (fun x=> -A x) p:=by simpa using h.scale (-1)
lemma free :DrySlot L s t a 0 (fun _=>0) p:=by
 refine ⟨_,_,fun S=>Suite.free S,⟨le_rfl,fun i=>?_,fun i=>?_⟩,fun i=>?_,fun _ _ _=>rfl⟩ <;> simp [saleM]
lemma sums {J:Type*}(U:Finset J)(k:J→ℝ)(f:J→Raw D I)(h:∀ i∈U,DrySlot L s t a (k i) (f i) p):DrySlot L s t a (∑ j∈U,k j) (fun x=>∑ j∈U,f j x) p:=by
 classical
 induction U using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact free
 | @insert i g e ih=> simp only [sum_insert e]; exact (h i (mem_insert_self i g)).plus (ih (fun j hj=>h _ (mem_insert_of_mem hj)))
lemma dry_erase (h:DrySlot L s t a q A p)(e:d≤a)(w:q≤k):DrySlot L s t d k A p:=by
 obtain ⟨F,C,g,l,u,t⟩:=h
 refine ⟨F,C,g,?_,u,t⟩
 exact (l.lowers (fun S i v=>mul_le_mul_of_nonneg_right (rent_up e S) ((g S).nonn i v))).book w
end DrySlot
lemma DrySlot.impose {p:D→Prop}{A:Raw D I}{a r:ℝ}(h:DrySlot L s t a r A p)(f:D→D)(hp:Continuous f) (e:∀ g d,f (b.drive g d) = b.drive g (f d))(hq:∀S x y,b.eval S (f x) (f y)=b.eval S x y)(hk:∀ g:D→ℂ,L.valid g→L.valid (fun x=> star (g (f x)))) (u:∀ x,p x→p (f x)): DrySlot L t s a r (fun x=> star (A (f x))) p:=by
  obtain ⟨F,C,p,l,Q,q⟩:=h
  let M (S:Seal Y)(x:D):=star (F S (f x))
  have hl(S):Suite L t s S (fun i j=> C S j i) (M S):=by
    refine ⟨?_,fun i j=>hk _ ((p S).fuel j i)⟩
    have hT:Ticket s t S (C S) (fun x=> F S (f x)):=by
      refine ⟨fun i x=> by rw [e]; exact (p S).frame ..,fun i j=>?_⟩
      have hx := (p S).expo i j
      exact ⟨hx.positive,hx.triggered,fun x=> hx.bounded _,fun x y=> by rw [← hq]; exact hx.variation .., hx.connected.comp hp⟩
    exact hT.starT
  exact ⟨M,_,hl,l.flip,fun x=> by dsimp only [M]; rw [Q,star_sum], fun S x v=>by dsimp only [M]; rw [q S (f x) (u x v),star_zero]⟩
end YM.CF.Drapes
end
