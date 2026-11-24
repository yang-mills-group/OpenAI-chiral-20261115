import YM.CF.Cubes.Assigned
import YM.CF.Lattice.Tenant
import YM.CF.Support.Hit

/-! Gathering connected supports into grid units. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset Branch Tenant
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
section abstract
variable {Y : Type*} [DecidableEq Y] {b : Branch.Field Y} {S : Finset Y}
lemma trek {x y : Y} (h : Grove b S) (g : x∈S) (e : y∈S) (k : ℕ) (p : k ≤ b.span x y) : ∃ z∈S,b.span x z=k := by
  have he : ∀ y, Origin b S x y→ k ≤ b.span x y→ ∃ z∈S,b.span x z=k := by
    intro z f; induction f with
    | refl => intro p; exact ⟨_,g,by rw [b.reflex] at p ⊢; omega⟩
    | @tail u v _ a ih =>
      intro p; by_cases l:k≤b.span x u
      · exact ih l
      refine ⟨v,a.2.1,?_⟩; have he := b.tri x u v; have hp := a.2.2; omega
  exact he _ (rooted h x g y e) p
lemma packed (h : Grove b S) (B : ℕ) : ∃ T:Finset Y, T⊆S ∧ T.card*B ≤ S.card+B ∧ ∀ x∈S, ∃ y∈T,b.span x y≤2*B := by
  let F := S.powerset.filter fun A=> ∀ x∈A, ∀ y∈A, x≠y→ 2*B<b.span x y
  obtain ⟨T,H,w⟩ := F.exists_max_image Finset.card ⟨∅,by simp [F]⟩
  obtain ⟨u,p⟩ := mem_filter.mp H; have hT := mem_powerset.mp u
  refine ⟨T,hT,?_,fun x g=>?_⟩
  · by_cases l:T.card≤1
    · apply (Nat.mul_le_mul_right B l).trans; omega -- tune
    let K (i:Y) := S.filter fun y=> b.span i y ≤ B
    have hk : T.biUnion K ⊆ S := by intro x hx; obtain ⟨i,_,he⟩ := mem_biUnion.mp hx; exact (mem_filter.mp he).1
    have he := card_le_card hk
    have hl (x) (A:x∈T) : B ≤ (K x).card := by
      have hw : (T.erase x).Nonempty := by rw [←card_pos,card_erase_of_mem A]; omega
      obtain ⟨y,hy⟩ := hw; obtain ⟨Q,f⟩ := mem_erase.mp hy; have ht := p x A y f Q.symm
      have hb : range B ⊆ (K x).image (b.span x) := by
        intro k g; have hp := mem_range.mp g
        obtain ⟨t,f,T⟩ := trek h (hT A) (hT f) k (by omega); exact mem_image.mpr ⟨t,mem_filter.mpr ⟨f,T ▸ hp.le⟩,T⟩ -- tune
      simpa only [card_range] using (card_le_card hb).trans card_image_le
    rw [card_biUnion] at he
    · have hm : T.card*B≤S.card := by
        calc T.card*B=∑ x∈T, (fun _=>B) x := by simp
             _ ≤ _ := (sum_le_sum hl).trans he
      omega
    intro x hx y hy l; apply disjoint_left.mpr; intro z f g
    have hp := b.tri x z y; rw [b.sym z y] at hp; have hQ := p x hx y hy l; have hf := (show b.span x z≤B from (mem_filter.mp f).2); have hG : b.span y z≤B := (mem_filter.mp g).2; omega
  by_contra! k
  have hl : x∉T := fun l=>by have hp:= k x l; rw [b.reflex] at hp; omega
  have he : insert x T ∈ F := by
    apply mem_filter.mpr; refine ⟨mem_powerset.mpr (insert_subset g hT),?_⟩
    intro i hi j hj l
    rcases mem_insert.mp hi with a|a <;> rcases mem_insert.mp hj with q|q
    · subst j i; tauto
    · subst i; exact k j q
    · subst j; rw [b.sym]; exact k i a
    exact p i a j q l
  have hp := w (insert x T) he; rw [card_insert_of_notMem hl] at hp; omega
end abstract

variable {m B : Side}
lemma distance_addr_iff (x y : Index m) (i : ℕ) : separation x y ≤ i ↔ separation (address m B x) (address m B y) ≤ B.val*i := by
  unfold separation pdist; rw [Finset.sup_le_iff,Finset.sup_le_iff]
  constructor <;> intro h j hj
  · change delta1 _ (address m B x j) (address m B y j)≤_
    unfold address; rw [high_here, high_here,d_high]; exact Nat.mul_le_mul_left _ (h j hj)
  have hk := h j hj; change delta1 _ (address m B x j) (address m B y j) ≤ _ at hk; unfold address at hk; rw [high_here,high_here,d_high] at hk; exact Nat.le_of_mul_le_mul_left hk B.property
-- allow sufficient halos for incidence, snapped face data and symmetrization.
def lands (m B : Side) (x : Site (Domain m B)) := (univ : Finset (Index m)).filter fun i=> x∈room m B i
def pavilion (m B : Side) (S : Support (Domain m B)) := S.biUnion fun x=> (lands m B x).biUnion fun i=>halo 6 {i}
lemma pad_iff (S : Support (Domain m B)) (x) : x∈pavilion m B S ↔ ∃ y∈S,∃ i:Index m,y∈room m B i ∧ separation i x≤6 := by simp [pavilion,lands,halo_spec] -- tune
lemma near_room {a b : Index m} {x y} (h:x∈room m B a) (g:y∈room m B b) (k : ℕ) (e : separation x y≤ k*B.val) : separation a b≤k+2 := by
  apply (distance_addr_iff (B:=B) a b _).mpr
  have he := room_span h; have hh := room_span g
  apply (separation_triangle _ x _).trans ((add_le_add ((separation_comm _ _).trans_le he) ((separation_triangle x y _).trans (add_le_add e hh))).trans ?_)
  rw [mul_add,Nat.mul_comm B.val k]; omega
lemma pad_slab {S : Support (Domain m B)} {z : Index m} {x} (g : slab m B z x) (h:x∈S) : z∈pavilion m B S := by
  obtain ⟨a,e,-⟩ := full_r m B x; apply (pad_iff S z).mpr; refine ⟨x,h,a,e,?_⟩; exact (near_room e (snapped g) 1 ((snap_sharp g).trans ((collar_lt B).le.trans_eq (one_mul _).symm))).trans (by omega)
lemma pad_hit {S : Support (Domain m B)} (i) (h:i∈pavilion m B S) : ∃ x∈S,separation (address m B i) x≤7*B.val := by
  obtain ⟨x,h,y,f,p⟩ := (pad_iff ..).mp h
  refine ⟨x,h,?_⟩; have he := (distance_addr_iff (B:=B) _ _ _).mp p
  rw [separation_comm]; apply (separation_triangle _ (address m B y) _).trans; have ht := add_le_add (room_span f) he; omega -- tune
lemma pad_small {S : Support (Domain m B)} (h : Grove (terr _) S) : (pavilion m B S).card * B.val ≤ 21^4 * (S.card+B.val) := by
  obtain ⟨T,H,K,L⟩ := packed h B.val
  choose a ha _ using fun t =>full_r m B t
  let A (z) := halo 10 {a z}
  have ht : pavilion m B S⊆T.biUnion A := by
    intro i hi; obtain ⟨x,g,j,k,e⟩ := (pad_iff ..).mp hi
    obtain ⟨y,g,p⟩ := L x g
    change separation x y≤_ at p; rw [separation_comm] at p
    exact mem_biUnion.mpr ⟨y,g,halo_spec.mpr ⟨a y,mem_singleton_self _,(separation_triangle _ j _).trans (add_le_add (near_room (ha y) k 2 p) e)⟩⟩
  have he z : (A z).card ≤ 21^4 := by
    unfold A; exact (Corona.halo_size ..).trans (by norm_num)
  have hp := (card_le_card ht).trans ((card_biUnion_le).trans (sum_le_sum (fun i _=>he i)))
  rw [sum_const,nsmul_eq_mul] at hp; apply (Nat.mul_le_mul_right B.val hp).trans; rw [mul_comm _ (21^4), mul_assoc]; exact Nat.mul_le_mul_left _ K
lemma pad_grove {S : Support (Domain m B)} (h : Grove (terr _) S) : Grove (terr _) (pavilion m B S) := by
  suffices H : ∀ z : Site (Domain m B), Grove (terr _) (pavilion m B {z}) by
    induction h with
    | single x => exact H x
    | @join S x y g e p ih =>
      obtain ⟨i,hx,_⟩ := full_r m B x; obtain ⟨j,hy,_⟩ := full_r m B y
      rw [show pavilion m B (insert x S)=pavilion m B S∪pavilion m B {x} by simp [pavilion,union_comm]]
      apply ih.unite (H x) ((pad_iff ..).mpr ⟨y,e,j,hy,(near_room hy hx 1 ?_).trans (by omega)⟩) ((pad_iff ..).mpr ⟨x,mem_singleton_self x,i,hx,by simp⟩)
      rw [one_mul]; exact (separation_comm ..).trans_le (p.trans B.property)
  intro z; let A := pavilion m B {z}; obtain ⟨i,e,_⟩ := full_r m B z
  have hm j (h:z∈room m B j) : halo 6 {j}⊆A := by intro x hx; obtain ⟨k,hk,h⟩ := halo_spec.mp hx; rw [mem_singleton.mp hk] at h; exact (pad_iff ..).mpr ⟨z,mem_singleton_self z,j,by assumption,h⟩
  apply trunk ((pad_iff (m:=m) (B:=B) {z} i).mpr ⟨z,mem_singleton_self z,i,e,by simp⟩)
  intro x hx; obtain ⟨k,hk,j,hj,H⟩ := (pad_iff ..).mp hx; rw [mem_singleton.mp hk] at hj
  have ht := near_room hj e 0 (by simp); apply orig_sub (T:=A) (rooted (glen j 6) i (by rw [bay_mem]; exact ht.trans (by omega)) x ((bay_mem _).mpr H))
  rw [tract]; exact hm j hj
-- precise labels read

def chairs (m B : Side) (S : Support (Domain m B)) : Support (GridN m) := S.biUnion fun i=> (active m B i).biUnion (faces m)
def walls (m B : Side) (S : Support (Domain m B)) : Support (Domain m B) := S∪(pavilion m B S).biUnion (room m B)
lemma chaff {S : Support (Domain m B)} {a} : a∈chairs m B S ↔ ∃ x∈S,∃ i∈active m B x,Fits m a i := by simp [chairs,faces] -- tune
lemma chair_pad {S : Support (Domain m B)} : chairs m B S⊆pavilion m B S := by
  intro i hi; obtain ⟨x,h,a,k,e⟩ := chaff.mp hi
  obtain ⟨t,p,q⟩ := full_r m B x; exact (pad_iff ..).mpr ⟨x,h,t,p,(fits_separation (fits_trans e (room_active p k))).trans (by omega)⟩
lemma in_wall {S : Support (Domain m B)} {x : Index m} (h:x∈pavilion m B S) : room m B x ⊆ walls m B S := fun _ he=> mem_union_right _ (mem_biUnion.mpr ⟨_,h,he⟩)
end YM.CF.Cube
