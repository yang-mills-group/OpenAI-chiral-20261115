import YM.CF.Petal.Stream

/-! Arbitrary union sizes. Accessible subsets entropy bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Filter Function Finset Branch NormedSpace
variable {I Y : Type*} [DecidableEq I] [DecidableEq Y] {X : I→Seal Y} {w : I→ℝ}
def heavy (w : I→ℝ) (S : Seal I) := ∏ i∈S,w i
def gild (B : Seal Y) (X : I→Seal Y) (w : I→ℝ) (S : Seal I) := ∑ i∈ tuft B X S, heavy w i
def hose (X : I→Seal Y) (z : Y) (S : Seal I) := S.filter fun i=> z∈X i
lemma trunk_cost {S : Seal I} (B : Seal Y) {p : Finset (Seal I)} (u : ∀ i∈p,i⊆S∧Attach X B i) (j : I) (H : j∈S) (w : I→ℝ) (k : ∀ i∈S,0≤w i) : ∑ i∈p.filter (fun A=>j∈A), heavy w i ≤ w j*gild (B∪X j) X w (S.erase j) := by -- k j if j∉S fail add
  let R := B∪X j; let C := p.filter fun i=>j∈i; let D (A:Seal I) := A.erase j
  have he (i) (h:i∈C) : D i∈ tuft R X (S.erase j) := by
    obtain ⟨f,l⟩:=mem_filter.mp h; obtain ⟨s,a⟩:= u i f; exact tuft_mem.mpr ⟨erase_subset_erase j s,fun k v=> (a k (mem_of_mem_erase v)).erase (mem_erase.mp v).1⟩
  have hp (i) (h:i∈C) : heavy w i=w j*heavy w (D i) := by nth_rw 1 [← insert_erase (a:=j) (mem_filter.mp h).2]; exact prod_insert (notMem_erase j i)
  have hj : Set.InjOn D C := fun x l y q h=> by
    change x.erase j=y.erase j at h; rw [← insert_erase (a:=j) (mem_filter.mp (show x∈C from l)).2,h]; exact insert_erase (mem_filter.mp (show y∈C from q)).2
  change ∑ i∈C, heavy w i ≤ _; rw [sum_congr rfl hp,←mul_sum]; unfold gild
  apply mul_le_mul_of_nonneg_left _ (k j (by assumption))
  rw [←sum_image hj]
  have hA : C.image D ⊆ tuft (B∪X j) X (S.erase j) := by intro i ht; obtain ⟨x,p,rfl⟩:=mem_image.mp ht; exact he x p
  refine sum_le_sum_of_subset_of_nonneg hA ?_
  intro i l _; exact prod_nonneg (fun i f=> k i (mem_of_mem_erase ((tuft_mem.mp l).1 f)))
lemma plugs (B : Seal Y) (z : Y) {p : Finset (Seal I)} (S : Seal I) (u : ∀ i∈p,i ⊆ S ∧ Attach X B i) (g : ∀ i∈p, ∃ j∈i,z∈X j) (k : ∀ i∈S,0 ≤ w i) : ∑ i∈p, heavy w i ≤ ∑ j∈hose X z S, w j*gild (B∪X j) X w (S.erase j) := by
  let H := hose X z S
  suffices he : ∑ i∈p, heavy w i ≤ ∑ j∈H,∑ i∈p.filter (fun i=>j∈i), heavy w i from he.trans (sum_le_sum fun j q=>trunk_cost B u j (mem_filter.mp q).1 w k) -- add
  simp_rw [sum_filter,sum_comm (s:=H)]; apply sum_le_sum; intro i h; obtain ⟨j,q,e⟩:= g i h
  have hv : 0≤heavy w i := prod_nonneg (fun x l=> k x ((u i h).1 l))
  exact le_trans (show heavy w i ≤ if j∈i then heavy w i else 0 by rw [if_pos q]) (single_le_sum (f:=fun j=> if j∈i then heavy w i else 0) (fun j _=>by split <;> simp [hv]) (mem_filter.mpr ⟨(u i h).1 q,e⟩))
-- cost hull: log 2 per labelled extent cancels attachment loss. Induct twice
lemma turn_p (S : Seal I) (B : Seal Y) (k : ∀ i∈ S,0≤w i) (j : ∀ z,∑ i∈hose X z S, w i*2^(X i).card ≤ 1/2) : gild B X w S≤2^B.card := by
  classical
  induction S using Finset.strongInductionOn generalizing B with
  | _ S ih=>
    induction B using Finset.induction_on with
    | empty=>
      have ht : tuft ∅ X S={∅} := by
        ext i; rw [mem_singleton]; constructor
        · intro v; by_contra p; obtain ⟨b,h⟩:=nonempty_iff_ne_empty.mpr p; obtain ⟨u,g,w⟩:= ((tuft_mem.mp v).2 _ h).lets; simp at w
        rintro rfl; exact tuft_zero ..
      simp [gild,ht,heavy]
    | insert z B hz ih'=>
      let b := insert z B; let A := tuft B X S; let E := tuft b X S; let F := E \ A
      have he : A ⊆ E := fun i g=>tuft_mem.mpr ⟨(tuft_mem.mp g).1,fun j l=> ((tuft_mem.mp g).2 j l).grows (subset_insert ..)⟩
      have hu (i) (h:i∈F) := tuft_mem.mp (mem_sdiff.mp h).1
      have hg (i) (h:i∈F) : ∃ j∈i,z∈X j := by
        by_contra! l
        apply (mem_sdiff.mp h).2; refine tuft_mem.mpr ⟨(hu i h).1,fun j p=>?_⟩
        have hx := ((hu i h).2 j p).eraseB l; rwa [show b.erase z=B from erase_insert hz] at hx
      let C : ℝ := 2^B.card; have hC : 0≤C := by unfold C; positivity
      have hv i (u:i∈hose X z S) : w i * gild (b∪X i) X w (S.erase i) ≤ 2*C*(w i*2^(X i).card) := by
        have p : i∈S := (mem_filter.mp u).1
        have hl : S.erase i ⊂ S := erase_ssubset p; have he := k i p
        have ht := ih (S.erase i) hl (b∪X i) (fun j v=>k j (mem_of_mem_erase v)) (fun x=> le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (erase_subset ..)) (fun i p _=> mul_nonneg (k i (mem_filter.mp p).1) (by positivity))) (j x))
        refine (mul_le_mul_of_nonneg_left ht he).trans ?_
        calc
          _ ≤ w i * 2^(b.card+(X i).card) := by gcongr <;> first | exact card_union_le b _ | norm_num -- tune
          _ = _ := by rw [pow_add (2:ℝ),show b.card=B.card+1 from card_insert_of_notMem hz,pow_succ]; unfold C; ring
      have hQ : ∑ i∈F,heavy w i ≤ C := by
        apply (plugs b z S hu hg k).trans ((sum_le_sum hv).trans ?_); rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left (j z) (by positivity : 0≤2*C)).trans_eq (by ring)
      change ∑ i∈E, heavy w i≤ 2^b.card; rw [← sum_sdiff he] -- tune name order
      exact (add_le_add hQ ih').trans_eq (by unfold C; unfold gild at *; rw [show b.card=_+1 from card_insert_of_notMem hz,pow_succ]; ring)
variable {S : Seal I} {a : ℝ}
lemma extract_hit (z : Y) (k : ∀ i∈S,0≤w i) (q : ∀ z,∑ i∈hose X z S,w i*2^(X i).card≤a) (p : a ≤ 1/2) : ∑ i∈(tuft {z} X S).erase ∅, heavy w i ≤ a := by
  let T := (tuft {z} X S).erase ∅; have hu (i) (h:i∈T) := tuft_mem.mp (mem_erase.mp h).2
  have hg (i) (h:i∈T) : ∃ j∈i,z∈X j := mem_biUnion.mp ((hu i h).2.meets (nonempty_iff_ne_empty.mpr (mem_erase.mp h).1))
  apply (plugs {z} z S hu hg k).trans ((sum_le_sum _).trans (q z)); intro i u
  have he : i∈S := (mem_filter.mp u).1; apply mul_le_mul_of_nonneg_left _ (k i he)
  have hx : z∈X i := (mem_filter.mp u).2; rw [union_eq_right.mpr (singleton_subset_iff.mpr hx)]
  refine turn_p _ _ (fun j v=>k j (mem_of_mem_erase v)) fun x=>?_
  exact (le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (erase_subset ..)) (fun i p _=> mul_nonneg (k i (mem_filter.mp p).1) (by positivity))) ((q x).trans p))
variable [Fintype Y]
lemma bio_bound (p : 0≤a) : rent a (roof X S) ≤ heavy (fun x=> rent a (X x)) S := by
  induction S using Finset.induction_on with
  | empty=> simp [roof_empty,rent,heavy]
  | insert i S h ih=>
    rw [roof, biUnion_insert]; unfold heavy; rw [prod_insert h]; exact (rent_join _ _ p).trans (mul_le_mul_of_nonneg_left ih (rent_pos ..).le)
lemma two_bound (S : Seal I) (X : I→Seal Y) : (2:ℝ)^(roof X S).card ≤ heavy (fun x=>(2:ℝ)^(X x).card) S := by
  induction S using Finset.induction_on with
  | empty=> simp [roof_empty,heavy]
  | insert i S h ih=>
    rw [roof,biUnion_insert]; unfold heavy; rw [prod_insert h]; apply le_trans ?_ (mul_le_mul_of_nonneg_left ih (by positivity)); rw [←pow_add]; gcongr <;> first | exact card_union_le (X i) (roof X S) | norm_num
lemma two_res (S : Seal Y) : (2:ℝ)^S.card ≤ rent 1 S := by
  unfold rent; rw [mul_comm 1,Real.exp_nat_mul]; apply pow_le_pow_left₀ zero_le_two; have hp := Real.add_one_le_exp (1:ℝ); linarith
lemma escrow (p : 0≤a) (k : ∀ i∈S,0≤w i) (q : ∀ z,∑ i∈hose X z S, rent (a+2) (X i) * w i ≤ 1/4) (x:Y) : ∑ i∈(tuft {x} X S).erase ∅, rent a (roof X i) * heavy w i * 2^(roof X i).card ≤ 1/4 := by
  let L (i:I) := rent a (X i)*w i*2^(X i).card
  have he i (h:i∈S) : 0≤L i := mul_nonneg (mul_nonneg (rent_pos ..).le (k i h)) (by positivity)
  have ht z : ∑ i∈hose X z S,L i * 2^(X i).card ≤ 1/4 := by
    apply (sum_le_sum _).trans (q z); intro i p; let T:= X i; let V:ℝ:=2^T.card; have hl := k i (mem_filter.mp p).1; have hi:=rent_pos a T; have hV:0≤V:=by unfold V; positivity; --semicolon tune
    have hx : rent a T * w i*rent 1 T*rent 1 T=rent (a+2) T * w i := by
      rw [mul_right_comm _ (w i), mul_right_comm _ (w i)]; unfold rent; rw [←Real.exp_add,←Real.exp_add]; congr 2; ring
    change rent a T*w i*V*V≤_; rw [← show rent a T*w i*rent 1 T*rent 1 T=rent (a+2) (X i)*w i from hx]; have ht := rent_pos 1 T; gcongr <;> first | positivity | exact two_res T
  apply (sum_le_sum _).trans (extract_hit x he ht (by norm_num)); intro i hx
  have hr : i⊆ S := (tuft_mem.mp (mem_erase.mp hx).2).1
  have hh : 0≤heavy w i := prod_nonneg (fun j p=>k j (hr p))
  have hg := bio_bound (X:=X) (S:=i) p
  have hp := two_bound i X
  simp_rw [heavy,L,prod_mul_distrib]; apply mul_le_mul (mul_le_mul_of_nonneg_right hg hh) hp (by positivity) (mul_nonneg ((rent_pos ..).le.trans hg) hh)
end YM.CF.Petal
