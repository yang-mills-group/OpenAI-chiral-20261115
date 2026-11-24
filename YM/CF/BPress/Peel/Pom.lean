import YM.CF.BPress.Peel.Trial
/-! geometry of roof enquiries. Poly use `potions` $on visits$. -/
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
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{q : A.Index} -- tune
abbrev reachP (x:A.Index) (t:ℕ) := halo t (A.gap x)
variable {p n j:ℕ}
lemma reach_m (u j:ℕ)(h:u≤j): reachP q u ⊆ reachP q j:= Corona.halo_mono h le_rfl
-- $Δ$ use station OR tangent? choose narrow, same time. plan projection.
def Room (l:A.Index)(S:Seal (BlockY A R))(u t:ℕ):= (reachP l u).filter fun x=>plan A R x∈ petal S t
lemma petal_m (a b:ℕ) (h:a≤b) : petal T a⊆petal T b:=by intro i p; obtain ⟨x,p,t⟩:=mem_biUnion.mp p; exact mem_biUnion.mpr ⟨x,p,stem_mid x h t⟩
lemma petal_grow {x y:BlockY A R}(h:x∈petal T j)(p:y∈Peel.stem x n): y∈petal T (j+n):=by obtain ⟨x,h,t⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨x,h,stem_join t p⟩
lemma rooms_m {m a:ℕ}(v:j ≤n)(q':m≤a): Room q S j m ⊆ Room q S n a:= fun i h=> mem_filter.mpr ⟨reach_m _ _ v ((mem_filter.mp h).1), petal_m _ _ q' ((mem_filter.mp h).2)⟩
lemma space_tang(x y:Site (More N))(p:moment A (x 0)=moment A (y 0)) (t:separation x y≤ R.L.val):plan A R y∈ Peel.stem (plan A R x) 1:= (stem_t ..).2 ⟨p.symm,tang_rad R _ _ ((Wealth.tail_sep ..).trans t)⟩
lemma extend_(x y:Site (More N))(v:x∈Room q S p n)(h:p+j≤ Wealth.cloak B)(z:j≤ R.L.val)(l:separation x y≤j): y∈Room q S (p+j) (n+1):=by obtain ⟨a,t⟩:=mem_filter.mp v; have hv:= crew_eq A l a; exact mem_filter.mpr ⟨hv,petal_grow t (space_tang x y ((moment_p A ((Nat.le_add_right ..).trans h) a).trans (moment_p A h hv|>.symm)) (l.trans z))⟩
lemma petalsInStation(p:ℕ)(h:p≤fixedR) : petal E p⊆ Contour.station fan E := by intro i v; obtain ⟨t,h',v⟩:= mem_biUnion.mp v; exact mem_biUnion.mpr ⟨t,h', stem_bay _ _ (stem_mid t h v)⟩
lemma roomPtr {Z:A.Hcols} (h:own A R Z∈ petal E p) (v:BlockY A R)(g:v∈ Peel.stem (own A R Z) n)(f:p+n≤fixedR): v∈Contour.station fan E:= petalsInStation (p+n) f (petal_grow h g)
lemma head (H:Crew A)(x:Choir A R)(t:i∈ Place H x) :∃ S∈Camp x H,i∈ S:=by rw [← reconstruct fan (Place H x)] at t; exact mem_biUnion.mp t -- tune `Parts.attr`
lemma memberQ (H:Crew A) (x:Choir A R){j:BlockY A R}(v:i∈Place H x)(b:S∈Camp x H)(p:j∈ S)(h:(shape A R).span i j≤ fixedR+fixedR) : i∈ S:=by
 obtain ⟨Z,F,q⟩:= head H x v; by_contra k; have hb:Z≠S:= fun x=> k (x ▸ q); exact (meets_core A R fixedR i j|>.2 h) (((Palmer.separate fan (Place H x) F b hb):Disjoint (Contour.station fan Z) (Contour.station fan S)).mono (subset_biUnion_of_mem _ q) (subset_biUnion_of_mem _ p)) -- tune
end YM.CF.BPress.Peel
