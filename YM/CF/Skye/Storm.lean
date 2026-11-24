import YM.CF.Skye.Zap
import YM.Work.E01
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical
variable {n:Side}{u d:ℝ}
abbrev legs(M:Finset (Seat n))(k:ℕ)(i j:Seat n):Prop := i ∈ M ∧ j∈ M ∧ separation i j ≤ 2*k+20
abbrev Cake(M:Finset (Seat n))(k:ℕ)(e:reach n):= M.filter fun j=>∃ i∈ends e,separation i j ≤ k
def soup(M:Finset (Seat n))(k:ℕ)(e: reach n):Finset (Seat n):= M.filter fun i=>∃ v ∈Cake M k e, Relation.ReflTransGen (legs M k) v i
lemma cake_p(M:Finset (Seat n))(k:ℕ)(e: reach n): Cake M k e=M ∩ win k e:=by ext; simp [Cake,win,halo_spec]
lemma soup_p(M:Finset (Seat n))(k:ℕ)(e:reach n):Cake M k e⊆soup M k e:=fun x hx=> Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,x,hx,.refl⟩
lemma pieV(M:Finset (Seat n))(k:ℕ)(e:reach n): (soup M k e).Nonempty ↔ ¬ Disjoint M (win k e):=by
 rw [Finset.disjoint_iff_inter_eq_empty,←cake_p,←ne_eq,←nonempty_iff_ne_empty]; refine ⟨fun g=>?_,fun t=>Nonempty.mono (soup_p ..) t⟩; obtain ⟨i,hx⟩:=g; obtain ⟨_,v,h,-⟩:=mem_filter.mp hx; exact ⟨_,h⟩
lemma dives {a b:reach n}{M:Finset (Seat n)}{k:ℕ}(g: (soup M k b).Nonempty)(h:∀ i∈ ends a,∀ j ∈ ends b,separation i j≤ 20): soup M k a⊆soup M k b:=by
 intro i hi; obtain ⟨v,hx,y⟩:= (mem_filter.mp hi).2; obtain ⟨w,t⟩:= (show (M ∩ win k b).Nonempty from nonempty_iff_ne_empty.mpr (fun u=> ((pieV M k b).mp g) (Finset.disjoint_iff_inter_eq_empty.mpr u)))
 rw [←cake_p] at t; refine Finset.mem_filter.mpr ⟨(mem_filter.mp hi).1,w,t,Relation.ReflTransGen.head ?_ y⟩
 obtain ⟨x,hh,p⟩:= (mem_filter.mp hx).2; obtain ⟨z,u,d⟩:= (mem_filter.mp t).2
 refine ⟨(mem_filter.mp t).1,(mem_filter.mp hx).1,?_⟩; have hp:=h x hh z u; have ht:=separation_triangle x z w; have hb:=separation_triangle w x v; rw [separation_comm w x] at hb; omega
lemma suppC(S M X: Finset (Seat n))(k:ℕ)(e:reach n) (p:S∩X=M∩X)(hp:win k e ⊆ X) (t:∀ i∈soup S k e, halo (2*k+20) {i}⊆X)(q:∀ i∈soup M k e, halo (2*k+20) {i}⊆X): soup S k e=soup M k e:=by
 have hh {S M:Finset (Seat n)}(p:S∩X=M∩X) (t:∀ i∈soup S k e, halo (2*k+20) {i}⊆X):soup S k e⊆soup M k e:=by
    intro i hi
    obtain ⟨a,v,g⟩:=(mem_filter.mp hi).2
    have ht :a∈Cake M k e:=by
       rw [cake_p] at v ⊢; rw [← Finset.inter_eq_right.mpr hp,← Finset.inter_assoc,←p,Finset.inter_assoc,Finset.inter_eq_right.mpr hp]; exact v -- hp mismatch
    have he: Relation.ReflTransGen (legs M k) a i:=by
       induction g with
       | refl => exact .refl
       | @tail b c r h ih =>
          have hg:b∈ soup S k e:=Finset.mem_filter.mpr ⟨h.1,a,v,r⟩; exact Relation.ReflTransGen.tail (ih hg) ⟨(Finset.mem_inter.mp (show b∈M∩ X from p ▸ Finset.mem_inter.mpr ⟨h.1,t b hg (by simp [halo_spec])⟩)).1,(Finset.mem_inter.mp (show c∈M∩ X from p ▸ Finset.mem_inter.mpr ⟨h.2.1,t b hg (halo_spec.mpr ⟨_,mem_singleton_self _,h.2.2⟩)⟩)).1,h.2.2⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (show i∈ M∩ X from p ▸ Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).1,t i hi (by simp [halo_spec])⟩)).1,a,ht,he⟩
 exact Finset.Subset.antisymm (hh p t) (hh p.symm q)
lemma cakeU (M:Finset (Seat n))(s:Sweep n)(k:ℕ)(e:reach n):Cake (M.map (boxA s).symm.toEmbedding) k e=(Cake M k (lane s e)).map (boxA s).symm.toEmbedding:=by ext x; rw [cake_p,cake_p,win,win,laneX,paysT]; simp -- cake_p,win,laneX, paysT]
lemma soupS (M:Finset (Seat n))(s:Sweep n)(k:ℕ)(e:reach n):soup (M.map (boxA s).symm.toEmbedding) k e=(soup M k (lane s e)).map (boxA s).symm.toEmbedding:=by
 set U := M.map _; have hx(i):i∈ U↔boxA s i∈ M:=by unfold U; simp
 have hh i j: legs U k i j ↔ legs M k (boxA s i) (boxA s j):=by simp only [legs,hx,sitT]
 have he i j: Relation.ReflTransGen (legs U k) i j ↔ Relation.ReflTransGen (legs M k) (boxA s i) (boxA s j):=by
    refine ⟨fun t=> Relation.ReflTransGen.lift (boxA s) (fun _ _ h=> (hh _ _).mp h) _ _ t,fun v=>?_⟩
    have hl: Relation.ReflTransGen (legs U k) ((boxA s).symm (boxA s i)) ((boxA s).symm (boxA s j)):=Relation.ReflTransGen.lift (boxA s).symm (fun i j (h:legs M k i j)=> (hh ((boxA s).symm i) ((boxA s).symm j)).mpr (show legs M k (boxA s ((boxA s).symm i)) (boxA s ((boxA s).symm j)) by rwa [Equiv.apply_symm_apply,Equiv.apply_symm_apply])) _ _ v; simpa using hl
 ext x; rw [mem_map_equiv]; change (_ ∈ soup U k e) ↔ (boxA s x ∈ soup M k (lane s e)); simp only [soup,mem_filter,hx,he,U,cakeU,mem_map_equiv]; rw [Equiv.symm_symm];
 apply and_congr_right; intro v; constructor; rintro ⟨i,h,g⟩; exact ⟨_,h,g⟩; rintro ⟨i,h,g⟩; obtain ⟨y,rfl⟩ := (boxA s).surjective i; exact ⟨y,h,g⟩
end YM.CF.Skye
