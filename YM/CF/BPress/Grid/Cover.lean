import YM.CF.BPress.Grid.Cube
import Mathlib.Order.Interval.Finset.Nat
/-! Connected-support packing argument in lem:B-frames and other costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Grid
open Function Finset Lattice Cube Branch
open scoped Topology BigOperators Classical
section grove
variable {F : Type} [Fintype F] [DecidableEq F] {A:Branch.Field F}
lemma inhabited_grove {S} (h:Grove A S): S.Nonempty:=by induction h <;> simp
-- thicken, independent of neighborhood. coverage numbers use connectivity at scale 1.
def broad {F : Type} [Fintype F] [DecidableEq F](A:Branch.Field F)(S : Finset F)(r:ℕ):= S.biUnion fun i=> bay A i r
@[simp] lemma broad_mem (A:Branch.Field F)(S : Finset F)(r:ℕ)(i:F): i∈broad A S r ↔ ∃ j∈S,A.span j i≤r:= by simp [broad]
lemma sphere_path (A : Branch.Field F) (S:Finset F) (t:Grove A S) {x y : F}(u:x∈S)(v:y∈ S) (i:ℕ) (p:i ≤ A.span x y) : ∃ z∈ S,A.span x z=i:=by
  have h(a:F)(e:Origin A S x a) : i ≤ A.span x a → ∃ z∈ S,A.span x z=i:=by induction e with
  | refl => intro t; rw [A.reflex] at t; exact ⟨_,u,by rw [A.reflex]; omega⟩
  | @tail b c _ e ih=>
    intro p; by_cases h:i≤ A.span x b; exact ih h
    have he := A.tri x b c; exact ⟨_,e.2.1, Nat.le_antisymm (by have h:=e.2.2; omega) p⟩
  exact h _ (rooted t x u y v) p

lemma cover_g (A : Branch.Field F) (S : Finset F) (t : Grove A S)(r:ℕ) : ∃ T ⊆ S, S ⊆ broad A T (2*r) ∧ r*T.card ≤ S.card+r:=by
 let q(s:Finset F):Prop:= s⊆ S ∧ (s:Set F).Pairwise fun i j=>2*r < A.span i j; have qt:q ∅:=by simp [q]
 let V:=univ.filter q
 obtain ⟨T,a,h⟩:= V.exists_max_image card ⟨_,mem_filter.mpr ⟨mem_univ _,qt⟩⟩
 obtain ⟨hT,b⟩:= (mem_filter.mp a).2; refine ⟨T,hT,?_,?_⟩
 · intro x p; by_contra u; have ht(i)(p:i ∈ T) : 2*r < A.span i x:= Nat.lt_of_not_ge fun t=> u ((broad_mem ..).mpr ⟨i,p,t⟩); have hz:x∉ T:=fun p=>by have t:=ht x p; rw [A.reflex] at t; omega
   have he:=h (insert x T) (show insert x T∈ V from mem_filter.mpr ⟨mem_univ _,insert_subset p hT,?_⟩); rw [card_insert_of_notMem hz] at he; omega
   intro i hi j hj l; rcases mem_insert.mp hi with f|f <;> rcases mem_insert.mp hj with g|g
   · exact (l (f.trans g.symm)).elim
   · rw [f,A.sym]; exact ht j g
   · rw [g]; exact ht i f
   exact b f g l
 by_cases e:T.card≤1; exact le_trans (mul_le_mul' le_rfl e) (by simp)
 have hx(i:F)(p:i∈T): r ≤ (bay A i r∩ S).card:=by
    obtain ⟨j,q,l⟩:= exists_mem_ne (show 1<T.card by omega) i -- tune
    have he:= b p q (Ne.symm l)
    apply le_trans (b:=((bay A i r∩S).image (A.span i)).card) _ card_image_le
    nth_rw 1 [← card_range r]; apply card_le_card; intro k g; rw [mem_range] at g; obtain ⟨z,v,K⟩:=sphere_path A S t (hT p) (hT q) k (by omega); exact mem_image.mpr ⟨z,mem_inter.mpr ⟨by simp [K,g.le],v⟩,K⟩
 have hb : (T:Set F).PairwiseDisjoint (fun i=> bay A i r∩ S):=by
    intro i hi j hj l; apply disjoint_left.mpr; intro a u v; have p := b hi hj l; have q: A.span i j≤ A.span i a+A.span j a:= (A.tri ..).trans_eq (by rw [A.sym a]); have hu: A.span i a ≤ r:= (bay_mem _).mp (mem_inter.mp u).1; have hv: A.span j a ≤r:= (bay_mem _).mp (mem_inter.mp v).1; omega
 have hl : T.biUnion (fun i=> bay A i r∩ S) ⊆ S:= by simp
 calc
  _ = ∑ i∈T,r:= by simp [mul_comm]
  _ ≤ _:=sum_le_sum hx
  _ ≤ _:= (card_biUnion hb).symm.le.trans ((card_le_card hl).trans (by omega))
end grove

variable {d r t k:ℕ} {s:Side}
-- packing on the period torus. scale-invariant bound on aligned grid population in one ball.
private lemma back_aligned (h:r ∣ s.val) (x y:Per s) (p:aligned x r) (q:aligned y r)(l:delta1 s x y ≤ k*r)(v:0<r) :
    ∃ a:ℤ, a.natAbs≤k ∧ y=x + (↑(a*(r:ℤ)) : Per s) := by
  let A:= y-x; have ht : aligned A r := by
    apply aligned_of_add h (k:= x.val) _ _ p; unfold A; rw [ZMod.natCast_zmod_val,sub_add_cancel]; exact q
  have he:(r:ℤ) ∣ A.valMinAbs:= by rw [ZMod.valMinAbs_def_pos]; split; exact_mod_cast ht; exact dvd_sub (by exact_mod_cast ht) (by exact_mod_cast h)
  obtain ⟨j,v'⟩:=he
  refine ⟨j,?_ ,?_⟩
  · rw [d_sym y x] at l; change (A.valMinAbs).natAbs ≤ _ at l; rw [v',Int.natAbs_mul] at l; apply Nat.le_of_mul_le_mul_left _ v; change r*j.natAbs ≤ r*k; rw [mul_comm r k]; exact l
  rw [mul_comm j,←v',ZMod.coe_valMinAbs]; unfold A; abel

lemma local_count (h:r ∣ s.val) (S : Finset (Space d s))(u : Space d s)(p: S ⊆ bay (field d s) u (k*r))(q:∀ i∈ S, i∈mesh r)(v:0<r) : S.card ≤ (4*k+1)^d:=by
  rcases S.eq_empty_or_nonempty with x|x; rw [x,card_empty]; omega
  obtain ⟨w,t⟩:=x; let Z:= Icc (-(2*(k:ℤ))) (2*(k:ℤ)); let V:= Fintype.piFinset fun _:Fin d=> Z; let f(x:Fin d→ℤ): Space d s:=fun i=> w i+ (↑(x i * (r:ℤ)):Per s)
  have hs:S ⊆ V.image f := by
    intro x hx; have ht : delta w x ≤ (2*k)*r:= by rw [mul_assoc,two_mul (k*r)]; exact (delta_triangle w u x).trans (add_le_add (le_trans (delta_comm ..|>.le) ((bay_mem ..).mp (p t))) ((bay_mem ..).mp (p hx)))
    choose z e l using fun i:Fin d=> back_aligned h (w i) (x i) (q w t i) (q x hx i) ((delta_at ..).trans ht) v
    exact mem_image.mpr ⟨z,Fintype.mem_piFinset.mpr fun i=> mem_Icc.mpr (by have h:=e i; omega),funext fun i=>(l i).symm⟩
  have hx:Z.card=4*k+1:=by rw [Int.card_Icc]; omega
  apply le_trans (card_le_card hs); apply card_image_le.trans_eq; simp [V,hx]
lemma around (h:r∣s.val)(S: Finset (Space d s))(p:Grove (field d s) S)(k:ℕ)(v:0<r) :
    r * ((broad (field d s) S (k*r)).filter (·∈mesh r)).card ≤ (4*(k+2)+1)^d*(S.card+r) := by
 obtain ⟨T,t,u,l⟩:= cover_g (field d s) S p r
 let V(i):= (bay (field d s) i ((k+2)*r)).filter (·∈mesh r); let N:= (4*(k+2)+1)^d; let X:= (broad (field d s) S (k*r)).filter (·∈mesh r)
 have H:X⊆ T.biUnion V:= by
   intro i q; obtain ⟨i',g,he⟩:= (broad_mem ..).mp (mem_filter.mp q).1; obtain ⟨j,t,p⟩:= (broad_mem ..).mp (u g); refine mem_biUnion.mpr ⟨j,t,mem_filter.mpr ⟨?_,(mem_filter.mp q).2⟩⟩; apply (bay_mem _).mpr; apply ((field d s).tri _ i' _).trans; rw [add_mul, add_comm (k*r)]; exact add_le_add p he
 have he:= (card_le_card H).trans (card_biUnion_le.trans ((sum_le_sum (g:=fun _=>N) (fun i (_:i∈T)=> local_count h (V i) i (filter_subset ..) (fun t h=>(mem_filter.mp h).2) v)).trans_eq (by simp : ∑ i∈ T,N=T.card*N)))
 exact le_trans (mul_le_mul_left' he r) ((by rw [←mul_assoc,mul_comm] : r * (T.card*N) ≤ N*(r*T.card))|>.trans (Nat.mul_le_mul_left N l)) -- tune
end YM.CF.BPress.Grid
