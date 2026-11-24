import YM.SU5.FiniteGaugeData.Hierarchy.Zone
/-!
 # True locality: bounded W-read Locators **intersect**, despite all-period support rule.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Portent
variable (K:Calibration) (S T : Finset Cover) (U : Finset Cover) {m n:Side}
lemma meet (p : Hosp (S∪T) n) : region (S∩T) n = region S n∩ region T n := by
  ext i; constructor
  · intro h; exact mem_inter.mpr ⟨image_subset_image inter_subset_left h,image_subset_image inter_subset_right h⟩
  intro h
  obtain ⟨a,b⟩ := mem_inter.mp h
  obtain ⟨x,hx,rfl⟩ := mem_image.mp a; obtain ⟨y,hy,k⟩ := mem_image.mp b
  obtain rfl : y=x := p.seat_ (mem_union_right _ hy) (mem_union_left _ hx) k
  exact mem_image_of_mem _ (mem_inter.mpr ⟨hx,hy⟩)
lemma sand (S T : Support (More n)) (x y : Pane n) (p : Agrees (↑(S∩T) : Set _) x y) :
    ∃ z : Pane n, Agrees S x z ∧ Agrees T z y := by
  let z : Pane n := fun a => if a.1∈S ∧ a.1+step a.2∈S then x a else y a
  refine ⟨z,fun a l r=>?_,fun a l r=>?_⟩
  · exact (if_pos (And.intro l r)).symm
  unfold z; split
  · next h=> exact p a (mem_inter.mpr ⟨h.1,l⟩) (mem_inter.mpr ⟨h.2,r⟩)
  rfl
lemma glob (p : T ⊆ S) (h : Hosp S n) (x : FC (Single n)) (v : Fine (Tset n) (modesIn n (region T n)) false x)
    (a : Key S) (g : selector S h a x ≠ 0) : staves (Typeset S a) T := by
  intro i k
  obtain ⟨u,b,rfl⟩ := List.mem_map.mp k
  have t : a.val.map (occupy S n h) ⊆ modesIn n (region T n) := by
    by_contra k
    exact g (by rw [selector_apply, (Advance.sub_plain v).cold k, mul_zero])
  have H := t (Finset.mem_map_of_mem (occupy S n h) (by simpa using b : u ∈ a.val))
  obtain ⟨⟨i,j,zq⟩,J⟩ := u
  change Lifted.index n i j zq ∈ modesIn n (region T n) at H
  rw [modes_at] at H
  change node (wrap n i) ∈ region T n at H; rw [node_of] at H
  obtain ⟨y,d,e⟩ := mem_image.mp H
  exact (h.seat_ (p d) J e) ▸ d
lemma rami (h : Hosp (S∪T) (K.c m)) {f : Mark (K.c m)}
    (p : AtSupport false (region S (K.c m)) f) (q : AtSupport false (region T (K.c m)) f) :
    AtSupport false (region (S∩T) (K.c m)) f := by
  constructor
  · exact p.env
  · intro x y a b
    rw [meet S T h] at a b
    obtain ⟨r,l,t⟩ := sand _ _ _ _ a; obtain ⟨u,v,k⟩ := sand _ _ _ _ b
    exact (p.dep x (r,u) l v).trans (q.dep (r,u) y t k)
  intro x
  have P := p.mono (image_subset_image (show S⊆S∪T from subset_union_left))
  rw [← analyze K _ h (P.allV x)]
  apply Fine.sumF
  intro a _
  by_cases u : selector (S∪T) h a (f x) = 0
  · rw [u,zero_smul]; exact .empty _
  apply Fine.scale
  have V : staves (Typeset (S∪T) a) (S∩T) := fun i k=> mem_inter.mpr
    ⟨glob _ S subset_union_left h _ (p.allV x) a u i k, glob _ T subset_union_right h _ (q.allV x) a u i k⟩
  rw [← spool_sing K m _ x, ← show treble (Typeset (S∪T) a) = false from a.property]
  exact ((sung K _ V (w:=true)).support m).allV x
lemma Lands (x : Charm.W K) (p : Charm.Locator K x S) (q : Charm.Locator K x T) : Charm.Locator K x (S∩T) := by
  -- union & smaller intersection roomy (always have after moving m, but x itself fixed)
  obtain ⟨m,hs,hu⟩ := ((roomy_sides (S∩T) K).and (roomy_sides (S∪T) K)).exists
  let P : Hosp (S∪T) (K.c m) := roomy_hosp _ hu
  obtain ⟨u,e⟩ := into_catalog (S∩T) K hs (rami K S T P ((show InTest K true S false x.val from p).support m) ((show InTest K true T false x.val from q).support m))
  have t := compose_t (S∩T) K u
  have H : x.val = composeQ K (S∩T) u := family_eq K (S∪T) P
    (Charm.locate_sub K p (T:=S∪T) subset_union_left) (t.mono (Subset.trans inter_subset_left subset_union_left)) e.symm
  unfold Charm.Locator; rwa [H]
#print axioms Lands
end Portent
end YM.CF.Buffered.Afterglow.Hierarchy
