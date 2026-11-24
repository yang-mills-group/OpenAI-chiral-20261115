import YM.CF.BPress.Lilac.Span
/- bookkeeping (pointwise memberships W.D/F). λ on bad.Exact independent.$
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Along Spine Mosaic.Pulse Mosaic Palmer Contour Lilac.Stripe Ledger Push.AbsoluteSums
variable {R: Hangar (More N)} (H:Crew A){I:Type}[Fintype I]
variable {T Q: SlotT A R}{o b i:BlockY A R} {x y: Choir A R}
def debris(x: Choir A R)(Q:SlotT A R): SlotT A R:= debts H x∩ Q
def untouch (b:SlotT A R):= petal b 29
abbrev Vista(x:Choir A R)(Q:SlotT A R):= untouch (debris H x Q)
def Upper(x: Choir A R) (Q: SlotT A R):= Q \ Vista H x Q
variable {H}
lemma estate0 (w:o∈ T): o∈Contour.station fan T:= mem_biUnion.mpr ⟨o,w,own_gilt ..⟩
lemma vista_demand(p:o∈ Vista H x T): Peel.stem o 40 ⊆ Contour.station fan T:=by
 intro i v; obtain ⟨a,t,q⟩:=mem_biUnion.mp p; exact mem_biUnion.mpr ⟨a,(mem_inter.mp t).2, stem_bay a fixedR (stem_mid a (by norm_num [fixedR] :29+40≤fixedR) (stem_join q v))⟩ -- tune
lemma thinker (p:o∈ Vista H x T): o∈Contour.station fan T:= vista_demand p (stem_home ..)
lemma vista_near (p:o∈ Vista H x T): o∈vicinity H x:=by obtain ⟨y,t,b⟩:=mem_biUnion.mp p; exact mem_biUnion.mpr ⟨y,(mem_inter.mp t).1,b⟩
lemma dark_disj (x: Choir A R): ((Camp x H):Set _).PairwiseDisjoint (Vista H x):= fun i t j v k=> (separate fan (Peel.Place H x) t v k).mono (fun i f=> thinker f) (fun i f=> thinker f) -- tune
lemma lands (x:Choir A R): (Camp x H).biUnion (Vista H x)=vicinity H x:=by
 ext i; refine ⟨fun v=>?_,fun v=>?_⟩; · obtain ⟨i,t,p⟩:=mem_biUnion.mp v; exact vista_near p
 obtain ⟨i,t,v⟩:=mem_biUnion.mp v; obtain ⟨Q,t',h⟩:= Peel.head H x (fat_m x t); exact mem_biUnion.mpr ⟨Q,t', mem_biUnion.mpr ⟨i, mem_inter.mpr ⟨t,h⟩, v⟩⟩ -- tune
lemma sky_eq (p: T∈ Camp x H)(v:b∈ Contour.station fan T): b∈Vista H x T↔ b ∈ vicinity H x:=by
 refine ⟨vista_near,fun w=>?_⟩; obtain ⟨i,q,u⟩:= mem_biUnion.mp (lands x|>.symm ▸ w); have he : i=T:=Classical.byContradiction (fun h=>Finset.disjoint_left.mp (separate fan (Peel.Place H x) q p h) (thinker u) v) -- tactic rewrite
 exact he ▸ u
lemma upper_l (t:T∈Camp x H): Upper H x T=T \ vicinity H x:=by
 ext i; exact Finset.mem_sdiff.trans ((and_congr_right fun v=> not_congr (sky_eq t (estate0 v))).trans Finset.mem_sdiff.symm)
lemma upper_loc {w x:Choir A R}(p:Along w x T) : debris H w T=debris H x T∧ Upper H w T=Upper H x T:= by
 have ht:debris H w T=debris H x T:=by ext i; simp only [debris,mem_inter]; exact and_congr_left fun v=> debtP p v -- tune
 exact ⟨ht,(by unfold Upper Vista; rw [ht])⟩
lemma debts_X (H:Crew A) : Measurable fun x:Choir A R=> debts H x:= by
 apply askF; intro i; simp_rw [debt_m]; exact measurable_pi_apply (X:=fun _=> Realm B N R) i (unholy_flag _ _)
lemma debris_m(H:Crew A)(T:SlotT A R):Measurable fun x=>debris H x T:=(measurable_of_countable (fun t:SlotT A R=> t∩ T)).comp (debts_X H)
lemma upper_m(H:Crew A)(T:SlotT A R):Measurable fun x=>Upper H x T:= (measurable_of_countable fun x:SlotT A R=> T\untouch x).comp (debris_m ..)
lemma vista_m(H:Crew A)(T:SlotT A R):Measurable fun x=>Vista H x T:=(measurable_of_countable untouch).comp (debris_m ..)
lemma vista_card(t:SlotT A R): (untouch t).card ≤ t.card * estate 29:=by unfold untouch petal; refine card_biUnion_le.trans ((sum_le_sum (g:=fun _=>estate 29) (fun i _=>?_)).trans_eq (by simp)); exact (card_le_card (stem_bay ..)).trans (capacity ..)
-- overcount anchor fuel
abbrev clampS (S:SlotT A R)(t:ℕ) := S.biUnion (fun i=> positions A R i t)
lemma fuel (x:Site (More N))(S:SlotT A R)(p:plan A R x∈ S){n:ℕ}(t: NearBlock A n x): x∈ clampS S n:= mem_biUnion.mpr ⟨_,p,mem_filter.mpr ⟨mem_univ _,rfl,t⟩⟩ -- tune NearBlock
lemma fuel_cost (S:SlotT A R){t:ℕ}(q:t ≤ Wealth.cloak B): (clampS S t).card ≤ S.card*(R.L.val^3*(B.D+2*t+1)):= card_biUnion_le.trans ((sum_le_sum (fun i _=> pinned_cost A R i q)).trans_eq (by rw [sum_const,nsmul_eq_mul]; simp)) -- tune nat.cast
abbrev NotT(b:SlotT A R)(S:SlotT A R): SlotT A R:= S\ untouch b
end YM.CF.BPress.Huon
