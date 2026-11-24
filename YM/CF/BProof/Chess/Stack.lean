import YM.CF.BProof.Chess.Chess
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix ComplexOrder Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N L:Side}{i:Axis}{s t h z w:ℕ}
local notation "Trup"=> Scute N L i w
namespace Drum
variable {H:Obs N→ℝ}(D:Drum N L i w H)
open Scute
lemma amount {F:List (Scute N L i w)} (g:∀ x∈ F,x.length=s): F.prod.length=s*F.length:=by
 induction F with| nil=>simp| cons x y ih=> simp [g x List.mem_cons_self, ih (fun i t=>g i (List.mem_cons_of_mem _ t)), mul_add,add_comm]
lemma bar_stack (F:List (Scute N L i w))(p:field L F.prod.length ≤ (More N).val)(h:0<w): F.prod.bar=(flop bar F).prod :=by
 induction F with| nil=> exact bar_v 0| cons x y ih=> rw [List.prod_cons] at p ⊢; rw [bar_mul _ _ p h,flop_cons,List.prod_append,List.prod_singleton,ih]; rw [surge,field_add] at p; omega
include D
lemma cycle (x y:Scute N L i w)(s:ℕ)(v: home L ((x*y)^s).length N): price H ((x*y)^s)=price H ((y*x)^s):=by
 cases s with
 | zero=> simp
 | succ n=>
   have h(k:ℕ): x*(y*x)^k=(x*y)^k *x:=by induction k with|zero=>simp|succ k ih=> rw [pow_succ,pow_succ,←_root_.mul_assoc,ih]; simp only [_root_.mul_assoc]
   let Y := (y*x)^n*y; have ht:(x*y)^(n+1)=x*Y:=by rw [pow_succ, ←_root_.mul_assoc,←h,_root_.mul_assoc]
   have hk:(y*x)^(n+1)=Y*x:=by rw [pow_succ, ←_root_.mul_assoc]
   rw [ht] at v ⊢; rw [hk]; exact D.circle x Y v
omit D
section
variable {α:Type*} {f:α→Scute N L i w}{π:α→α}
structure Tack (π:α→α)(s:ℕ)(f:α→Scute N L i w):Prop where
 inv : Involutive π
 size (x:α): (f x).length=s
 spin (x:α): f (π x)=(f x).bar
namespace Tack
abbrev stack (f:α→Scute N L i w)(x:List α):= (x.map f).prod
@[simp] lemma chat (x y:List α): stack f (x++y)=stack f x*stack f y:=by simp [stack]
variable (g:Tack π s f)
include g
lemma num (x:List α): (stack f x).length=s*x.length:=by rw [stack,amount (fun i t=> let ⟨v,t,k⟩:=List.mem_map.mp t; (k ▸ g.size v))]; simp
lemma tags (x: List α) : flop bar (x.map f)=(flop π x).map f:=by unfold flop; rw [List.map_reverse,List.map_map,List.map_map, show bar ∘ f=f∘π from funext fun x=>(g.spin x).symm]
lemma storage (x:List α)(p:field L (s*x.length) ≤ (More N).val)(h:0<w): bar (stack f x)=stack f (flop π x):= (bar_stack (x.map f) (by simpa only [← g.num x] using p) h).trans (congrArg List.prod (g.tags x))
lemma stature(a:α)(b:ℕ): stack f (beat π a (2*b)) = (f a* (f a).bar)^b:=by
 rw [norep _ g.inv]; simp [stack,List.prod_flatten,g.spin]
end Tack
variable{n:ℕ} (T: halfC L N (s*n))(p:0<n)(g:Tack π s f)
include T p D g
lemma prices : Price n π (fun x=> price H (Tack.stack f x)):=by
 let B:=Tack.stack f; have ht(x:List α)(v:x.length=n): halfC L N (B x).length:=by unfold B; rw [g.num x,v]; exact T
 refine ⟨fun x _=> D.nonneg _,p,g.inv,fun x y v=>?_,fun x y p v=>?_⟩
 · rw [Tack.chat,Tack.chat]; apply D.circle; rw [g.num x,g.num y,←mul_add,v,two_mul,mul_add]; unfold home; rw [field_add, show field L (s*n)=_ from T, natM]; omega -- namespace mul_add theorem
 have hz:field L (s*n) ≤(More N).val:=by rw [show field L (s*n)=_ from T,natM]; omega
 rw [Tack.chat,Tack.chat,Tack.chat,←g.storage x (p.symm ▸ hz) D.pos,←g.storage y (v.symm ▸ hz) D.pos]; exact D.edge _ _ (ht x p) (ht y v)
lemma sign [Finite α](x:List α)(w:x.length=2*n):∃ a:α, price H (Tack.stack f x)≤price H ((f a*(f a).bar)^n):=by obtain ⟨v,t⟩:=(D.prices T p g).maximal x w; change _ ≤ price H (Tack.stack f (beat π v (2*n))) at t; rw [g.stature] at t; exact ⟨_,t⟩
end
end Drum
end YM.CF.BProof.Chess
