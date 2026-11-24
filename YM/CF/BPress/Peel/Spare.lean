import YM.CF.BPress.Peel.Roof
/- reader @plan block root. requires base equality (may need Frame for deep). Honors only visible I(Q). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Sugar.Crew Grid Env Bands Vesper Hazel Hazel.Letters Net
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}{R: Hangar (More N)}
open Palmer Contour Along Sheet
attribute [local instance] Gauge.frobInner
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{q : A.Index}{k r:ℕ}
variable {X:Stage N}{e c d :ℝ}{x y:Visit A R H}
variable (F:Rented R H X d e k c) (Q:Charter H R X k)
namespace Charter
include F Q
lemma to_read (A': Peek H t x.val y.val)(l:Link (More N))(h: Peel.stem (plan A R l.1) 2⊆ t)(f:H.port (fU x.val) l=H.port (fU y.val) l): H.utensil (fU x.val) l=H.utensil (fU y.val) l:=by
 let u:=plan A R l.1; let Z(v:Visit A R H):= Danger A R X.W (debts H v.val); have he:= (peeking t _ _ A').masks h (H:=H); by_cases p:l.1∈ Z x; swap
 · have ht(v:Visit A R H)(p:l.1∉ Z v): H.utensil (fU v.val) l= H.port (fU v.val) l:= by
    let b:= F.pay (fU v.val) v.property; exact F.roof.lamp _ _ _ (Classical.byContradiction (fun h=> p (b.dangerous l h|>.1)))
                                                                                                                      -- tune indent syntax
   rw [ht x p, ht y _]; exact f; intro q; obtain ⟨a,g⟩:= (mem_filter.mp q).2; exact p (mem_filter.mpr ⟨mem_univ _,a,he.2 g⟩)
 obtain ⟨a,g⟩:= (mem_filter.mp p).2; obtain ⟨s,v,d⟩:= mem_biUnion.mp (at_petal.mpr (show Local (debts H x.val) 2 u from g)); obtain ⟨S,p,r⟩:= head H x.val (fat_m x.val v); have hv:S∈ Visible fan t (Place H x.val):=mem_filter.mpr ⟨p,fun D=> disjoint_left.mp D (petalsInStation 2 (by norm_num [fixedR]) (mem_biUnion.mpr ⟨s,r,d⟩)) (h (stem_home ..))⟩; obtain ⟨q,Q'⟩:=a; exact Charter.comparison F Q p (mem_filter.mpr ⟨ (zone_of_halo A q X.W.U l.1).mpr Q', mem_biUnion.mpr ⟨s,r,d⟩⟩) (A'.watcher S hv) ((mem_filter.mp (show S∈ Visible fan t (Place H y.val) from A'.regular ▸ hv)).1) -- tune
end Charter
end YM.CF.BPress.Peel
