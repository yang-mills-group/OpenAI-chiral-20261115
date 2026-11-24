import YM.CF.Petal.Pace
set_option linter.unusedSectionVars false

/-! Accessible label packets, plucking the component at a site. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open Filter Branch Finset
open scoped BigOperators Topology
variable {Y I : Type*} [DecidableEq Y] [DecidableEq I]
inductive Web (X : I→Seal Y) (B : Seal Y) (S : Seal I) : I→Prop
  | low i : i∈S → ¬Disjoint (X i) B → Web X B S i
  | hop i j : Web X B S i→ j∈S→ ¬ Disjoint (X j) (X i)→ Web X B S j
variable {X : I→Seal Y} {B R : Seal Y} {S T : Seal I} {i j : I}
def crease (B : Seal Y) (X : I→Seal Y) (S : Seal I) := S.filter fun i=> Disjoint (X i) B
def roof (X : I→Seal Y) (S : Seal I) := S.biUnion X
lemma roof_empty : roof X ∅=∅ := by simp [roof]
lemma crease_r (z:Y) : crease {z} X S=S.filter fun i=> z∉ X i := by simp [crease]
lemma crease_m (X : I→Seal Y) (S : Seal I) (B R : Seal Y) : crease (B∪R) X S=crease R X (crease B X S) := by ext i; simp [crease,and_assoc]
lemma crease_sub (u : B⊆R) : crease R X S⊆ crease B X S := by
  intro a h; obtain ⟨g,p⟩:= mem_filter.mp h; exact mem_filter.mpr ⟨g,Disjoint.mono_right u p⟩
lemma roof_id {B} (h : T⊆crease B X S) : Disjoint (roof X T) B := by
  apply disjoint_left.mpr; intro j g l; obtain ⟨i,p,f⟩:= mem_biUnion.mp g; exact disjoint_left.mp (mem_filter.mp (h p)).2 f l
lemma roof_atom {i : I} (p : i∈S) : X i⊆ roof X S := fun _ h=> mem_biUnion.mpr ⟨i,p,h⟩
namespace Web
lemma active (h : Web X B S i) : i∈S := by cases h <;> assumption
lemma extend (h : Web X B S i) (p : S⊆T) : Web X B T i := by
  induction h with
  | low i g e=> exact .low i (p g) e
  | hop i j _ g e ih=> exact .hop _ j ih (p g) e
lemma grows (h : Web X B S i) (p : B⊆R) : Web X R S i := by
  induction h with
  | low i g e=> exact .low i g (fun h=>e (Disjoint.mono_right p h))
  | hop i j _ g e ih=> exact .hop _ _ ih g e
lemma distinct (h : Web X B S i) : (X i).Nonempty := by
  cases h with
  | low i _ g=> obtain ⟨x,p,q⟩:= not_disjoint_iff.mp g; exact ⟨x,p⟩
  | hop i j _ g p=> obtain ⟨x,v,_⟩:= not_disjoint_iff.mp p; exact ⟨x,v⟩
lemma lets (h : Web X B S i) : ∃ j∈S, ¬Disjoint (X j) B := by induction h with
  | low=> exact ⟨_,by assumption,by assumption⟩
  | hop _ _ _ _ _ ih=> exact ih
lemma basin {z:Y} {b : Branch.Field Y} (h : Web X {z} S i) (k : ∀ j ∈ S, Grove b (X j)) : z∈ roof X S ∧ ∀ y∈ X i, Origin b (roof X S) z y := by
  induction h with
  | low j p u=>
    have hu : z∈X j := by simpa using u
    exact ⟨roof_atom p hu,fun _ e=> orig_sub (rooted (k j p) _ hu _ e) (roof_atom p)⟩
  | hop j i h p u ih=>
    obtain ⟨x,hx,t⟩:= not_disjoint_iff.mp u
    exact ⟨ih.1,fun y e=> (ih.2 x t).trans (orig_sub (rooted (k i p) x hx y e) (roof_atom p))⟩
lemma erase (h : Web X B S i) (u : i≠j) : Web X (B∪X j) (S.erase j) i := by
  induction h with
  | low v e q => exact .low _ (mem_erase.mpr ⟨u,e⟩) (fun h=>q (Disjoint.mono_right subset_union_left h))
  | hop v t h w k ih=>
    have ht := mem_erase.mpr ⟨u,w⟩; by_cases l:v=j
    · subst v; exact .low _ ht (fun h=>k (Disjoint.mono_right subset_union_right h))
    exact .hop _ _ (ih l) ht k
lemma eraseB {z:Y} (h : Web X B S i) (p : ∀ j∈S,z∉ X j) : Web X (B.erase z) S i := by
  induction h with
  | low j p₁ v=>
    obtain ⟨x,H,W⟩:=not_disjoint_iff.mp v
    exact .low _ p₁ (not_disjoint_iff.mpr ⟨x,H,mem_erase.mpr ⟨fun f=> p _ p₁ (f ▸ H),W⟩⟩)
  | hop j k _ l v ih=> exact .hop _ _ ih l v
end Web
def Attach (X : I→Seal Y) (B : Seal Y) (S : Seal I) := ∀ i∈S, Web X B S i
lemma Attach.void : Attach X B ∅ := by simp [Attach]
lemma Attach.meets {y : Y} (u : S.Nonempty) (g : Attach X {y} S) : y∈roof X S := by -- auto implicit y?
  obtain ⟨i,H⟩ := u; obtain ⟨j,p,q⟩:= (g i H).lets; exact roof_atom p (by simpa using q)
lemma Attach.root (X : I→Seal Y) (B : Seal Y) {p : Seal I} (h : Attach X B S) (g : p⊆ crease (B∪roof X S) X T) : Disjoint S p := by
  apply disjoint_left.mpr; intro i k v; obtain ⟨j,H⟩:= (h i k).distinct; exact disjoint_left.mp (mem_filter.mp (g v)).2 H (mem_union_right _ (roof_atom k H))
attribute [local instance] Classical.propDecidable
def plume (B : Seal Y) (X : I→Seal Y) (T : Seal I) := T.filter (Web X B T)
def fib (B : Seal Y) (X : I→Seal Y) (T : Seal I) := T \ plume B X T
lemma plume_spec (B : Seal Y) (X : I→Seal Y) (T : Seal I) (i : I) : i∈plume B X T ↔ Web X B T i := ⟨fun h=>(mem_filter.mp h).2,fun h=>mem_filter.mpr ⟨h.active,h⟩⟩
lemma Attach.fibres (B : Seal Y) (X : I→Seal Y) (T : Seal I) {W : Seal I} (u : T⊆W) : fib B X T ⊆ crease (B∪roof X (plume B X T)) X W := by
  intro i k; obtain ⟨p,v⟩:=mem_sdiff.mp k; apply mem_filter.mpr; refine ⟨u p,?_⟩
  by_contra q; apply v; apply (plume_spec ..).mpr
  obtain ⟨j,g,h⟩:= not_disjoint_iff.mp q; rcases mem_union.mp h with l|l
  · exact .low _ p (not_disjoint_iff.mpr ⟨j,g,l⟩)
  obtain ⟨x,H,W⟩:= mem_biUnion.mp l; exact .hop _ _ ((plume_spec ..).mp H) p (not_disjoint_iff.mpr ⟨j,g,W⟩)
lemma Web.plant (h : Web X B T i) : Web X B (plume B X T) i := by
  induction h with
  | low h p q=> exact .low _ ((plume_spec ..).mpr (.low _ p q)) q
  | hop v t h f g ih=> exact .hop _ _ ih ((plume_spec ..).mpr (.hop _ _ h f g)) g
lemma fly (X : I→Seal Y) (B : Seal Y) (T : Seal I) : Attach X B (plume B X T) := fun i e=> ((plume_spec ..).mp e).plant
lemma Web.base (X : I→Seal Y) (B : Seal Y) {T S V : Seal I} (g : T ⊆ crease (B∪roof X S) X V) {i : I} (h : Web X B (S∪T) i) : i∈ S := by
  induction h with
  | low i p v=>
    rcases mem_union.mp p with l|l; exact l
    exact False.elim (v (Disjoint.mono_right subset_union_left (mem_filter.mp (g l)).2))
  | hop x i e h v ih=>
    rcases mem_union.mp h with l|l; exact l
    exact False.elim (v (Disjoint.mono_right (Subset.trans (roof_atom ih) subset_union_right) (mem_filter.mp (g l)).2))
lemma Attach.plumage (X : I→Seal Y) (B : Seal Y) {T S V : Seal I} (h : Attach X B S) (g : T⊆ crease (B∪roof X S) X V) : plume B X (S∪T)=S := by
  ext i; rw [plume_spec]; exact ⟨fun k=>Web.base X B g k,fun k=>(h i k).extend subset_union_left⟩
lemma Attach.shot (X : I→Seal Y) (B : Seal Y) {T S V : Seal I} (h : Attach X B S) (g : T⊆ crease (B∪roof X S) X V) : fib B X (S∪T)=T := by
  unfold fib; rw [Attach.plumage X B h g,union_sdiff_left]; exact sdiff_eq_self_of_disjoint (Attach.root X B h g).symm

def tuft (B : Seal Y) (X : I→Seal Y) (T : Seal I) := T.powerset.filter (Attach X B)
lemma tuft_mem {A : Seal I} : T∈tuft B X A ↔ T⊆ A ∧ Attach X B T := by simp [tuft]
lemma tuft_zero (B : Seal Y) (X : I→Seal Y) (T : Seal I) : ∅∈ tuft B X T := tuft_mem.mpr ⟨empty_subset _,Attach.void⟩
-- exact recombination
lemma plum (X : I→Seal Y) (B : Seal Y) (S : Seal I) {E : Type*} [AddCommMonoid E] (F : Seal I→E) : ∑ i∈S.powerset,F i=∑ i∈tuft B X S, ∑ j∈(crease (B∪roof X i) X S).powerset,F (i∪j) := by
  let t := tuft B X S; let p (i) := (crease (B∪roof X i) X S).powerset
  let g (x : Sigma (fun _ : Seal I=>Seal I)) := x.1∪x.2
  change _=∑ i∈t,∑ j∈p i,F (i∪j)
  rw [sum_sigma' (f:=fun i j=>F (i∪j))] -- tune
  symm; apply sum_bij (fun v _=> g v)
  · rintro ⟨x,y⟩ h; obtain ⟨u,v⟩:= mem_sigma.mp h
    exact mem_powerset.mpr (union_subset (tuft_mem.mp u).1 (Subset.trans (mem_powerset.mp v) (filter_subset ..)))
  · rintro ⟨x,y⟩ h ⟨s,z⟩ w l; obtain ⟨u,v⟩:= mem_sigma.mp h; obtain ⟨j,t⟩:=mem_sigma.mp w
    change x∪y=s∪z at l
    have hx : x=s := Eq.trans (Attach.plumage X B (tuft_mem.mp u).2 (mem_powerset.mp v)).symm ((congrArg (plume B X) l).trans (Attach.plumage X B (tuft_mem.mp j).2 (mem_powerset.mp t)))
    have ht : y=z := Eq.trans (Attach.shot X B (tuft_mem.mp u).2 (mem_powerset.mp v)).symm ((congrArg (fib B X) l).trans (Attach.shot X B (tuft_mem.mp j).2 (mem_powerset.mp t)))
    subst s z; rfl
  · intro b l; let A := plume B X b
    have he : A⊆b := filter_subset ..; have hB := mem_powerset.mp l
    refine ⟨⟨A,fib B X b⟩,mem_sigma.mpr ⟨tuft_mem.mpr ⟨Subset.trans he hB,fly X B b⟩,mem_powerset.mpr (Attach.fibres B X b hB)⟩,?_⟩
    exact union_sdiff_of_subset he
  intro i _; rfl
end YM.CF.Petal
