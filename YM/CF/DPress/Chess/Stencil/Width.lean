import YM.CF.Scroll.Coat
/-! Short stencils. Use the Brix column calculation in seplift, on its actual Fourier symbol.
We won't need optimal width or coefficient sizes: the scale budgets for fermion range are chosen
*after* the patch. Keep its exact matrices, using the alias sum with compact support, even price
all columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Symbol
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat
open scoped Topology BigOperators NNReal ENNReal Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{I J:Type*}{A B: Momentum→ℂ}
def Trig(f:Momentum→ℂ):Prop:=∃ S:Finset Cover,∃ τ: Cover→ℂ,∀ p:Momentum,physical p→ f p=∑ y∈S,mode p y*τ y
namespace Trig
lemma ux (i:Cover)(a:ℂ) :Trig (fun p=> mode p i*a):=⟨{i},fun _=>a,fun _ _=>by simp⟩
lemma tone (i:Cover):Trig (fun p=>mode p i) :=by have h:= ux i 1; simpa using h
lemma cong (h:Trig A)(p:∀ t,physical t→A t=B t):Trig B:=by obtain ⟨s,f,h⟩:=h; exact ⟨s,f,fun x hp=> (p x hp).symm.trans (h _ hp)⟩
lemma fixed (a:ℂ):Trig (fun _=>a):=(ux 0 a).cong (fun _ _=>by simp)
lemma pitch (S:Finset I)(τ:I→Cover)(f:I→ℂ)(p:∀ t,physical t→ A t=∑ i∈S,mode t (τ i)*f i):Trig A:=by
 let V:=S.image τ; refine ⟨V,fun i=>∑ j∈S with τ j=i,f j,fun x h=>?_⟩; rw [p x h,←sum_fiberwise_of_maps_to (t:=V) (g:=τ) (fun i hv=> mem_image_of_mem τ hv) (fun i=>mode x (τ i)*f i)]; apply Finset.sum_congr rfl; intro i _; dsimp only; rw [mul_sum]; exact Finset.sum_congr rfl fun a p=>by rw [(mem_filter.mp p).2] -- tune binder
lemma mul (f:Trig A)(p:Trig B): Trig (fun x=>A x*B x):=by
 obtain ⟨U,F,v⟩:=f; obtain ⟨V,G,u⟩:=p; apply pitch (U×ˢV) (fun i=> i.1+i.2) (fun i=>F i.1*G i.2); intro t p; rw [v t p,u t p,sum_product]; simp only [sum_mul,mul_sum,mode_shift]; rw [sum_comm]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl fun j _=>?_); ring
lemma add (f:Trig A)(p:Trig B): Trig (fun x=>A x+B x):=by
 obtain ⟨U,F,v⟩:=f; obtain ⟨V,G,u⟩:=p; apply pitch (U.disjSum V) (Sum.elim id id) (Sum.elim F G); intro x hp; rw [v x hp, u x hp,Finset.sum_disjSum]; rfl
lemma sum_v(S:Finset I)(p:I→Momentum→ℂ)(t:∀ i∈S,Trig (p i)): Trig (fun x=>∑ i∈ S,p i x):=by induction S using Finset.induction_on with|empty=> simpa using fixed 0|@insert i D h ih=> simp_rw [sum_insert h]; exact add (t i (mem_insert_self ..)) (ih (fun x u=> t x (mem_insert_of_mem u)))
lemma prod_v(S:Finset I)(p:I→Momentum→ℂ)(t:∀ i∈S,Trig (p i)): Trig (fun x=>∏ i∈ S,p i x):=by induction S using Finset.induction_on with|empty=> simpa using fixed 1|@insert i D h ih=> simp_rw [prod_insert h]; exact mul (t i (mem_insert_self ..)) (ih (fun x u=> t x (mem_insert_of_mem u)))
lemma pow_v (n:ℕ)(t:Trig A): Trig (fun p=> A p^n):=by induction n with|zero=> simpa using fixed 1|succ n ih=>simp_rw [pow_succ]; exact mul ih t
lemma twirl_t(i:Axis)(k:ℤ): Trig (fun p=>twirl (p i) k):=by
 refine (tone (Pi.single i k)).cong (fun p t=>?_); unfold mode twirl; rw [sum_eq_single i]; simp; ring -- tune
 intro b _ u; rw [Pi.single_eq_of_ne u,Int.cast_zero,mul_zero]; simp
lemma muffX (j:ℕ)(L:Side): Trig (muff j L):= pow_v _ (prod_v _ (fun i p=>plank L (p i)) (fun i _=> mul (twirl_t i _) (mul (fixed _) (sum_v (range L.val) (fun j (p:Momentum)=>twirl (p i) j) (fun j _=>twirl_t ..)))))
lemma roll (i:Cover)(L:Side): Trig (fun p=> ∑ l: Site L,mode (aliasAt p l) i):=by
 by_cases h:wrap L i=0; swap
 · refine (fixed 0).cong (fun p _=> ?_); simp_rw [aliasAt,mode_phase,←Bloch.cell_wrap,←mul_sum,show ∀ v:Site L,cell v _=cell (wrap L i) v from fun v=>cell_duality ..] -- tune last rewrite loops
   rw [sum_cell h,mul_zero]
 obtain ⟨k,g⟩:= cover_of_eq 0 i (by rw [map_zero,h]); rw [zero_add] at g; rw [g]; have ht(p:Momentum)(i:Site L):mode (aliasAt p i) (L.val • k)=mode p k:=by rw [←mode_scale L.val,alias_scale,mode_phase,mode_periodic,mul_one]
 simp_rw [ht]; simp only [sum_const,card_univ,nsmul_eq_mul]; exact (fixed _).mul (tone k)
lemma hord (u:Trig A)(L:Side): Trig (fun p=>∑ l:Site L,A (aliasAt p l)):=by
 obtain ⟨V,f,u⟩:=u; apply (sum_v V (fun i (p:Momentum)=> (∑ l:Site L, mode (aliasAt p l) i) * f i) (fun i _=>mul (roll i L) (fixed _))).cong; intro p v; simp only [u _ (alias_real v _)]; simp_rw [sum_mul]; rw [sum_comm]
end Trig
end YM.CF.DPress.Chess.Symbol
