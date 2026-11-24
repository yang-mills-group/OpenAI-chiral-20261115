import YM.CF.BPress.Peel.Tan
import YM.CF.BPress.Sugar.Stan
/-! canonical E = $innings$ on comparisons.Stem, standard producer one per block role. Peek with exact equality of visible cores. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Sugar.Crew Grid Env
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}{R: Hangar (More N)}
open Palmer Hazel Contour
attribute [local instance] Gauge.frobInner
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}
abbrev points (A:Bands (More N) B)(R:Hangar (More N))(H:Crew A)(x:Choir A R) := H.Role (House.read A R x)
-- classical frame.Sup. one certificate for whole state, includes valid barrel and noise
abbrev Visit(A:Bands (More N) B)(R:Hangar (More N))(H:Crew A):= {x:Choir A R// points A R H x}
abbrev Place(H:Crew A)(x:Choir A R) := innings A R H.y x
abbrev party (A:Bands (More N) B)(R:Hangar (More N))(H:Crew A)(x: Visit A R H): H.castP:= ⟨House.read A R x.val,x.property⟩
abbrev debts(H:Crew A)(x: Choir A R):= H.unsea R (House.read A R x)
abbrev Camp (x:Choir A R)(H:Crew A): Finset (Seal (BlockY A R)):= Palmer.Parts fan (Place H x)
lemma party_meas (h:Fast H.y) : Measurable (party (A:=A) R H):= by -- tune shadow A
 exact Measurable.subtype_mk ((recipe _ _ h).measurable.comp measurable_subtype_coe)
section temp
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
instance choirBorn : StandardBorelSpace (Choir A R):=by haveI: DiscreteMeasurableSpace (Spire.Sweep N):= ⟨fun _=> trivial⟩; haveI:PolishSpace SU.E:=inferInstance; haveI: StandardBorelSpace (Spire.Sweep N):=inferInstance; haveI:StandardBorelSpace (Skye.Ids N):=inferInstance; haveI:StandardBorelSpace (Hat N):=inferInstance; haveI:StandardBorelSpace (Platter (B:=B) R):=inferInstance; haveI:StandardBorelSpace (Encore (B:=B) R):=inferInstance; haveI:StandardBorelSpace (Attire (B:=B) R):=inferInstance; haveI:StandardBorelSpace (Bank R):=inferInstance; haveI: StandardBorelSpace (Realm B N R):=inferInstance; infer_instance
lemma visit_p (h: Fast H.y): StandardBorelSpace (Visit A R H):=by
 exact MeasurableSet.standardBorel ((recipe A R h).measurable H.Role_meas)
end temp
lemma pay_p(x:Choir A R) : P∈ Camp x H → P⊆ Place H x:= fun p=> (Palmer.lives _ _ p).1
lemma debt_m (x: Choir A R) : i ∈ debts H x ↔ unholy R H.y (x i):= unholy_body ..
lemma fat_m (x:Choir A R) : debts H x ⊆ Place H x:= fun i h=>mem_filter.mpr ⟨mem_univ _, succ_excite _ _ _ (debt_m x|>.1 h)⟩
lemma opt_m : Measurable (fun x:Choir A R=> Place H x):= askF _ (fun i=>by simp only [Place,innings,mem_filter,mem_univ,true_and]; exact measurable_pi_apply (X:=fun _=>Realm B N R) i (excite_meas (B:=B) R H.y)) -- tune meas space BlockY discrete
lemma opt_flags(x:Choir A R)(y : BlockY A R)(hy:y∈E) (t:x∈House.Ward A R H.y E) : excite R H.y (x y):= ((mem_filter (p:=fun i:BlockY A R=> excite R H.y (x i))).mp ((inning_eq ..).mp t ▸ (show y∈E from ‹_›))).2 -- parser unsupported binder
abbrev Along(x y:Choir A R)(V:Seal (BlockY A R)): Prop:= ∀ i∈V,x i=y i -- Habitat.Plain.Along diff
structure Peek (H:Crew A)(P: Seal (BlockY A R))(x y:Choir A R):Prop where
 regular: Visible fan P (Place H x)=Visible fan P (Place H y)
 run: Along x y (watches fan P (Place H x))
variable {x y: Choir A R}
lemma debtP (f:Along x y S)(p:i∈ S): i∈ debts H x ↔ i∈debts H y:= by rw [debt_m,debt_m,f i p]
lemma Along.mono (Q: Along x y S)(p:t⊆ S): Along x y t:=fun i t=> Q i (p t)
lemma Along.symm (Q: Along x y T):Along y x T:=fun i t=>(Q i t).symm
lemma peeking (P: Seal (BlockY A R))(x y:Choir A R)(h:Peek H P x y): Along x y P:= h.run.mono subset_union_left
namespace Peek
lemma watcher (T: Seal (BlockY A R))(v:T∈ Visible fan P (Place H x))(h:Peek H P x y) : Along x y (Contour.station fan T):= h.run.mono ((subset_biUnion_of_mem _ v).trans subset_union_right)
lemma stays(y x:Choir A R)(t:Peek H P x y): watches fan P (Place H x)= watches fan P (Place H y):=by unfold watches; rw [t.regular]
lemma swap (p:Peek H S x y): Peek H S y x:= ⟨p.regular.symm, p.stays y x ▸ p.run.symm⟩ -- tune dot
lemma pays {Q:Seal (BlockY A R)}(h:T⊆Q): Visible fan T E ⊆ Visible fan Q E:=fun i v=> mem_filter.mpr ⟨(mem_filter.mp v).1, fun t=> (mem_filter.mp v).2 (t.mono_right h)⟩ -- monotone
lemma less (g:Peek H T x y)(h:S⊆T) : Peek H S x y:=by
 have he(x y: Choir A R)(t:Peek H T x y)(i)(p:i∈ Visible fan S (Place H x)) : i∈ Visible fan S (Place H y):= mem_filter.mpr ⟨(mem_filter.mp (show _ from (show i∈ Visible fan T (Place H y) from t.regular ▸ pays h p))).1,(mem_filter.mp p).2⟩
 refine ⟨Subset.antisymm (fun i=> he x y g i) (fun i=>he y x g.swap i),g.run.mono (union_subset_union h ?_)⟩; intro i v; obtain ⟨j,v,g⟩:= mem_biUnion.mp v; exact mem_biUnion.mpr ⟨j,pays h v,g⟩
-- Core permit. When paying $G$, may need inherited read on support of each inner term attached, lying INSIDE I Q. Even if comparing different families this suffices for that $T$ read.
lemma island (h:T ⊆ Contour.station fan S)(x: Choir A R)(p:S∈ Camp x H)(v:T.Nonempty): Visible fan T (Place H x)={S}:=by
 ext i; constructor; · intro t; rw [mem_singleton]; refine Classical.byContradiction fun g=>?_ ; obtain ⟨q,t⟩:=mem_filter.mp t; exact t (((separate fan (Place H x) q p g):Disjoint (Contour.station fan i) (Contour.station fan S)).mono_right h)
 intro q; rw [mem_singleton.mp q]; refine mem_filter.mpr ⟨p,?_⟩; obtain ⟨x,t⟩:=v; exact fun f=> disjoint_left.mp f (h t) t
lemma inner (p:S ∈ Camp x H)(t:S∈ Camp y H)(g:Along x y (Contour.station fan S))(u:T⊆ Contour.station fan S) : Peek H T x y:=by
 rcases T.eq_empty_or_nonempty with e|e; · rw [e]; refine ⟨?_,?_⟩; simp [Visible]; simp [Along,watches,Visible]
 have hx:=island u _ p e; refine ⟨hx.trans (island u _ t e|>.symm), ?_⟩; unfold watches; rw [hx,singleton_biUnion]; exact g.mono (union_subset u le_rfl)
end Peek
end YM.CF.BPress.Peel
