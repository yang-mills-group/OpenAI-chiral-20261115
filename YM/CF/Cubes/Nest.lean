import YM.CF.Cubes.Vote

/-! Incidence structure and finite number of ancestors even on large tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat
open Finset
variable {m B : Side}

abbrev Index (m : Side) := Site (GridN m)
def os (m : Side) (a : Index m) := univ.filter (fun i => OddAxis m (a i))
def degree (m : Side) (a : Index m) := (os m a).card
lemma degree_le (m a) : degree m a ≤ 4 := card_le_univ _
def Fits (m : Side) (a b : Index m) := ∀ i, a i=b i ∨ (¬ OddAxis m (a i) ∧ OddAxis m (b i) ∧ delta1 (GridN m) (b i) (a i)≤1)
instance (a b) : Decidable (Fits m a b) := by unfold Fits; infer_instance
lemma fits_id (m a) : Fits m a a := fun _ => Or.inl rfl
lemma fits_trans {a b c} (h : Fits m a b) (g : Fits m b c) : Fits m a c := by
  intro i; rcases h i with he|he; rw [he]; exact g i
  rcases g i with hx|hx; rw [←hx]; exact Or.inr he; exact False.elim (hx.1 he.2.1)
lemma fits_separation {a b} (h : Fits m a b) : separation b a ≤ 1 := by
  unfold separation pdist; apply Finset.sup_le; intro i _; change delta1 _ (b i) (a i)≤1
  rcases h i with e|e; rw [e,d_id]; norm_num; exact e.2.2
lemma fits_os {a b} (h : Fits m a b) : os m a ⊆ os m b := fun i l => by
  rw [os,mem_filter] at l ⊢; rcases h i with e|e; simpa only [←e] using l; exact False.elim (e.1 l.2)
lemma fits_degree {a b} (h : Fits m a b) (g : a≠b) : degree m a < degree m b := by
  by_contra! e; apply g; have H : os m a=os m b := eq_of_subset_of_card_le (fits_os h) e
  funext i; rcases h i with l|l; exact l
  have hx : i∈os m a := H.symm ▸ mem_filter.mpr ⟨mem_univ i,l.2.1⟩; exact False.elim (l.1 (mem_filter.mp hx).2)
def faces (m : Side) (b : Index m) := univ.filter (fun a => Fits m a b)
lemma faces_bound (m b) : (faces m b).card ≤ (box 1).card := by
  let f : Cover → Index m := fun x=>b-wrap (GridN m) x
  apply le_trans _ (card_image_le (s:=box 1) (f:=f)); apply card_le_card; intro a h
  have g := fits_separation (m:=m) (a:=a) (b:=b) (mem_filter.mp h).2
  apply mem_image.mpr; refine ⟨lift (b-a),?_,?_⟩
  · have he (i : Axis) : ((lift (b-a)) i).natAbs≤1 := le_trans (component_le _ i) g
    rw [box_test]; constructor <;> intro i <;> have H := he i <;> omega
  · simp [f]

def ballot (m B : Side) (z : Site (Domain m B)) (a : Index m) (t : Coin B) := ∀ i, elect m B (z i) t (a i)
instance (z a t) : Decidable (ballot m B z a t) := by unfold ballot; infer_instance
lemma some_ballot (m B : Side) (z : Site (Domain m B)) (t : Coin B) : ∃ a, ballot m B z a t := by
  choose a ha using fun i => elect_some m B (z i) t
  exact ⟨a,ha⟩
def selected (m B : Side) (z : Site (Domain m B)) (t : Coin B) := (some_ballot m B z t).choose
lemma picked (m B z t) : ballot m B z (selected m B z t) t := (some_ballot m B z t).choose_spec
lemma picked_iff {z a t} : ballot m B z a t ↔ a=selected m B z t := ⟨fun g=>funext (fun i=>elect_unique (g i) (picked _ _ _ _ _)),fun h=>h ▸ picked m B z t⟩
def active (m B : Side) (z : Site (Domain m B)) := univ.image (selected m B z)
lemma select_mem (m B z t) : selected m B z t ∈ active m B z := mem_image.mpr ⟨t,mem_univ t,rfl⟩
lemma active_iff (z a) : a ∈ active m B z ↔ ∃ t, ballot m B z a t := by
  unfold active; simp only [mem_image,mem_univ,true_and,picked_iff]; simp [eq_comm]
lemma cmp_select (z : Site (Domain m B)) (t u) (h : t≤u) : Fits m (selected m B z u) (selected m B z t) := by
  intro i; rcases elect_mon (picked m B z t i) (picked m B z u i) (show _ from h) with g|⟨hx,hl,hf⟩
  · exact Or.inl g.symm
  exact Or.inr ⟨hl,hx,hf⟩
lemma chain {z a b} (h : a ∈ active m B z) (g : b∈ active m B z) : Fits m a b ∨ Fits m b a := by
  obtain ⟨t,-,rfl⟩ := mem_image.mp h; obtain ⟨u,-,rfl⟩ := mem_image.mp g
  exact (le_total u t).imp (cmp_select z u t) (cmp_select z t u)
lemma degreeInj (z : Site (Domain m B)) : Set.InjOn (degree m) (active m B z) := by
  intro a h b g e; by_contra he; rcases chain h g with hz|hz
  · exact (fits_degree hz he).ne e
  exact (fits_degree hz (Ne.symm he)).ne e.symm
lemma chain_len (z : Site (Domain m B)) : (active m B z).card ≤ 5 := by
  rw [← card_image_of_injOn (degreeInj z)]
  apply (card_le_card (t:=range 5) _).trans (by simp only [card_range,le_refl]); intro i hi
  obtain ⟨a,-,rfl⟩ := mem_image.mp hi; exact mem_range.mpr (lt_of_le_of_lt (degree_le ..) (by norm_num))

def address (m B : Side) (a : Index m) : Site (Domain m B) := (scaleR m B).root a
lemma node_dist {z a} (h : a ∈ active m B z) : separation z (address m B a) < B.val := by
  obtain ⟨t,ht⟩ := (active_iff ..).mp h
  unfold separation pdist; refine lt_of_le_of_lt (Finset.sup_le (a:=B.val-1) ?_) ?_
  · intro i _; change delta1 _ (z i) (address m B a i)≤_; unfold address; rw [high_here]
    have he := lt_of_le_of_lt (ht i) (radius_lt ..); omega
  have g : 0 < B.val := B.property; omega
lemma chain_near {a b} (h : Fits m a b) (B : Side) : separation (address m B b) (address m B a)≤B.val := by
  unfold separation pdist; refine Finset.sup_le ?_; intro i _
  change delta1 _ (address m B b i) (address m B a i)≤_; unfold address; rw [high_here,high_here,d_high]
  rcases h i with e|e; rw [e,d_id]; simp; exact (Nat.mul_le_mul_left _ e.2.2).trans (le_of_eq (mul_one _))
end YM.CF.Cube
