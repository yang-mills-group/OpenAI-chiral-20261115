import YM.CF.BProof.Grid.Connect
import YM.CF.BProof.Grid.Wire

/-! Range cost including connected support. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Function Finset MeasureTheory
open scoped BigOperators Classical
variable {n : ℕ}{s: Fin n → Side}

-- packing uses steps in S; for size k walk length not needed, height marks present.
lemma visits_all (S:Sites s)(h:Conn S 1)(x y : Vertex s)(hx:x∈S)(hy:y∈ S) (k:ℕ)(v:k≤dist x y) : ∃ z∈S,dist x z=k:=by
 induction h x hx y hy with
 | refl=> rw [dist_self] at v; exact ⟨x,hx,by rw [dist_self]; omega⟩
 | @tail y z t hp ih=>
   by_cases e:k≤dist x y; exact ih hp.1 e
   have ht:= (triangle x y z).trans (Nat.add_le_add_left hp.2.2 _); exact ⟨z,hp.2.1,by omega⟩
lemma packing (S:Sites s)(h:Conn S 1)(k:ℕ) : ∃ p:Sites s,p⊆ S ∧ p.card*k≤ S.card+k ∧ S⊆ collar p (2*k) := by
 classical
 let Pack (p:Sites s):Prop:= ∀ x∈p,∀ y∈p,x≠y→2*k<dist x y
 let A:= S.powerset.filter Pack; obtain ⟨p,hp,H⟩:= exists_max_image A Finset.card ⟨(∅:Sites s),mem_filter.mpr ⟨mem_powerset.mpr (empty_subset ..),by unfold Pack; simp⟩⟩; obtain ⟨hx,hp⟩:= mem_filter.mp hp; have hx:= mem_powerset.mp hx
 refine ⟨p,hx,?_,fun i hi=>?_⟩
 · by_cases g:p.card≤1; exact ((Nat.mul_le_mul_right k g).trans (by rw [one_mul]; omega))
   let f(x:Vertex s):= S.filter fun y=>dist x y≤k
   have he(x)(u:x∈p): k≤ (f x).card:=by
      obtain ⟨y,v,hy⟩:= Finset.exists_mem_ne (show 1<p.card from by omega) x
      have hk : range k ⊆ (f x).image (dist x):=by intro i hq; obtain ⟨z,v,hj⟩:= visits_all S h x y (hx u) (hx v) i (by have:= hp x u y v hy.symm; have := mem_range.mp hq; omega); exact mem_image.mpr ⟨z,mem_filter.mpr ⟨v,hj ▸ (mem_range.mp hq).le⟩,hj⟩
      exact (card_range k) ▸ ((Finset.card_le_card hk).trans card_image_le)
   calc
     _ = ∑ x∈p,k := by simp
     _ ≤ ∑ x∈p,(f x).card:=sum_le_sum he
     _ ≤ _:=by
        have ht:(p:Set (Vertex s)).PairwiseDisjoint f := by
           intro i hi j hj g; apply disjoint_left.mpr; intro a H h; have hv:= triangle i a j; rw [dist_symm a j] at hv; have hq:=hp i hi j hj g; have hw:= (mem_filter.mp H).2; have hx:= (mem_filter.mp h).2; omega
        rw [←card_biUnion ht]; exact le_trans (Finset.card_le_card (show p.biUnion f ⊆ S from Finset.biUnion_subset.mpr fun i _=> Finset.filter_subset ..)) (by omega)
 by_contra he; have hu : ∀ x∈p, 2*k<dist i x:=fun x hx=>lt_of_not_ge (fun h=> he (collar_mem.mpr ⟨_,hx,h⟩)); have hg : i∉p:= fun h=> by have := hu i h; rw [dist_self] at this; omega
 apply Nat.not_succ_le_self p.card; rw [Nat.succ_eq_add_one,← Finset.card_insert_of_notMem hg]; apply H; refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.insert_subset hi hx),?_⟩
 intro x a y b e; rcases mem_insert.mp a with h1|h1 <;> rcases mem_insert.mp b with h2|h2; exact False.elim (e (h1.trans h2.symm)); exact h1.symm ▸ hu y h2; subst y; rw [dist_symm]; exact hu x h1; exact hp x h1 y h2 e

section
variable {s c : Side}(g : Ratio c s) (m:ℕ)(S:Finset (Cubic n s))
def scout (S:Finset (Cubic n s))(m:ℕ):Finset (Cubic n c):= univ.filter fun i=> grow g i ∈ collar S (m*g.count.val)
lemma from_le {m r}(h:m≤r): scout g S m ⊆ scout g S r:=fun _ hx=> mem_filter.mpr ⟨mem_univ _,collar_le Subset.rfl (Nat.mul_le_mul_right _ h) (mem_filter.mp hx).2⟩ -- Subset.rfl maybe unknown

lemma sparseness (h:Conn S 1) : (scout g S m).card*g.count.val ≤ (2*(m+3)+1)^n * (S.card+g.count.val) := by
 obtain ⟨p,hp,u,X⟩:= packing S h g.count.val
 let r:=g.count.val
 have he : scout g S m⊆ collar (p.image (elder g)) (m+3):=by
   intro x hx; obtain ⟨y,hy,z⟩:= collar_mem.mp (mem_filter.mp hx).2; obtain ⟨i,k,hk⟩:= collar_mem.mp (X hy)
   refine collar_mem.mpr ⟨_,mem_image_of_mem _ k, (Nat.mul_le_mul_right_iff (by exact g.count.property : 0<r)).mp ?_⟩
   rw [show r=g.count.val from rfl,← reach]
   apply (triangle _ i _).trans; exact (Nat.add_le_add ((triangle _ y i).trans (Nat.add_le_add z hk)) (close ..)).trans (by rw [add_mul]; omega)
 have H : (scout g S m).card ≤ _ := (card_le_card he).trans (collar_volume ..); calc
   _ ≤ ((2*(m+3)+1)^n*p.card)*g.count.val:= Nat.mul_le_mul_right _ (H.trans (by rw [mul_comm _ p.card]; gcongr; exact card_image_le))
   _ ≤ _:=by rw [mul_assoc]; gcongr

-- Footprints for updating a query: include links at coarse reads all starting at
-- `from` sites. Extend via real long links and connectors bounded in finest lattice.
theorem rent (h: Conn S 1) : ∃ T,S⊆T∧ Conn T 1 ∧ T⊆collar S ((2*m+1)*g.count.val) ∧
    (∀ x∈scout g S m,grow g x∈T ∧ ∀ (i:Fin n) (a:ℕ),a ≤ g.count.val→jump (grow g x) i a ∈ T) ∧
    T.card ≤ S.card+ ((m+1+ n*2)*(2*(m+3)+1)^n)*(S.card+g.count.val) := by
 let W:=scout g S m; let r:=g.count.val; let V:=collar S ((2*m+1)*g.count.val); have hr:0<r:=g.count.property
 have H(x)(hx:x∈W): ∃ Q:Sites (fun _:Fin n=>s), Conn Q 1∧grow g x∈ Q∧(∃ i∈S,i∈Q)∧ Q⊆ V ∧ (∀ (i:Fin n) a,a≤ g.count.val→jump (grow g x) i a∈Q) ∧ Q.card ≤ (m+1+n*2)*r:= by
    let X:=grow g x; obtain ⟨y,hy,hb⟩:= collar_mem.mp (mem_filter.mp hx).2
    obtain ⟨p,hp,hv,K,U,k⟩:= Grid.attach X y (m*g.count.val) hb
    let F(i:Fin n):= road (jump X i) r
    have hm (i : Fin n):Conn (F i) 1:=track _ _ _ (fun k _=>by rw [jump_succ]; exact near_slide ..)
    have he(i):X∈ F i:= jump_zero X i ▸ mem_image_of_mem (jump X i) (mem_range.mpr (Nat.zero_lt_succ _))
    refine ⟨p ∪ univ.biUnion F,pile _ K F (fun i _=>hm i) (fun i _=>⟨_,hp,he i⟩),mem_union_left _ hp,⟨y,hy,mem_union_left _ hv⟩,fun i h=>?_,fun i a h=> mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ i,mem_image_of_mem (jump X i) (mem_range.mpr (Nat.lt_succ_of_le h))⟩),?_⟩
    · apply collar_mem.mpr; refine ⟨y,hy,(triangle _ X _).trans (le_trans (Nat.add_le_add_left hb _) ?_)⟩ -- tune
      rw [dist_symm i X]; rcases mem_union.mp h with h|h
      · have ht:= k i h; rw [add_mul,mul_assoc]; omega
      obtain ⟨j,-,x⟩:= mem_biUnion.mp h; obtain ⟨a,b,rfl⟩:= mem_image.mp x; have hl:= near_jump X j a; have hm:=mem_range.mp b; rw [add_mul,mul_assoc]; dsimp only [r] at hm; omega
    apply (card_union_le ..).trans; apply le_trans (Nat.add_le_add U (show (univ.biUnion F).card ≤ ∑ _ : Fin n,(r+1) from (card_biUnion_le).trans (sum_le_sum fun i _=>(show (F i).card≤r+1 from card_image_le.trans (by rw [card_range])))))
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; change m*r+1+n*(r+1)≤_; have ht:= Nat.mul_le_mul_left n (show r+1 ≤ 2*r from by omega); rw [add_mul,add_mul,mul_assoc]; omega
 choose! Q hQ hq Hv v q t using H
 refine ⟨S∪ W.biUnion Q,subset_union_left,pile W h Q hQ Hv, union_subset (to_collar ..) (Finset.biUnion_subset.mpr v),fun x hx=> ⟨mem_union_right _ (mem_biUnion.mpr ⟨x,hx,hq x hx⟩),fun i a h=> mem_union_right _ (mem_biUnion.mpr ⟨x,hx,q x hx i a h⟩)⟩,?_⟩ -- tune trans
 apply (card_union_le ..).trans; apply Nat.add_le_add_left; apply (card_biUnion_le.trans (sum_le_sum t)).trans; simp only [sum_const,nsmul_eq_mul]; have he:W.card*r ≤ _:= sparseness g m S h; exact le_trans (Eq.le (by ring : W.card*((m+1+n*2)*r)=(m+1+n*2)*(W.card*r))) ((Nat.mul_le_mul_left _ he).trans_eq (by rw [mul_assoc])) -- tune
end
end YM.CF.BProof.Grid
