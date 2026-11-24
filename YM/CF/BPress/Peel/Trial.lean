import YM.CF.BPress.Peel.Copy
/-! acceptance per core. Reads support & each component label, before orientation.any states. -/
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
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{x y: Choir A R} (p: Along x y S)
namespace Along
variable (u:Host R H)
include u p
lemma scope(i:A.Hcols)(v: Peel.stem (own A R i) 1⊆S)(k:SpatialDir): tower H (fU x) i.1 (i.2,k)=tower H (fU y) i.1 (i.2,k):=by unfold tower crownT window; rw [horizonDepth,horizonDepth]; exact p.sky_tap u.hearth u.size _ v
omit u p in
private lemma stacked (v:A.Hcols)(p:Peel.stem (own A R v) 2⊆ S) (k:SpatialDir): Peel.stem (own A R (v.1,hop v.2 k 1)) 1⊆S:=fun i t=>p (stem_join (r:=1) (t:=1) (step1 v k) t)
lemma scopeH (i:A.Hcols)(h: Peel.stem (own A R i) 2⊆ S) : H.T.hue H.y (tower H (fU x) i.1) i.2= H.T.hue H.y (tower H (fU y) i.1) i.2:= hue_screen _ _ _ _ _ (p.scope u i ((stem_mid _ (by norm_num)).trans h)) (fun j=>p.scope u (i.1,hop i.2 j 1) (stacked i h j)) -- tune stacked p includes u
lemma gives (i:A.Hcols)(h: Peel.stem (own A R i) 2⊆ S): H.T.give H.y (tower H (fU x) i.1) i.2 ((fU x).1.2 i)= H.T.give H.y (tower H (fU y) i.1) i.2 ((fU y).1.2 i):=by unfold Sheet.Atlas.give; rw [(p.controls i (h (stem_home ..))).2.1, p.scopeH u _ h]
lemma scopeP (i:A.Hcols)(h: Peel.stem (own A R i) 2 ⊆ S): H.T.passes H.y (tower H (fU x) i.1) i.2 ↔ H.T.passes H.y (tower H (fU y) i.1) i.2:=by
 have he(j k) : plaq (tower H (fU x) i.1) i.2 j k= plaq (tower H (fU y) i.1) i.2 j k:=by
    let d:= p.scope u i ((stem_mid _ (by norm_num)).trans h); let A(x):= p.scope u (i.1,hop i.2 x 1) (stacked i h x); unfold plaq; refine congrArg₂ (·*·) (congrArg₂ (·*·) (congrArg₂ (·*·) (d j) (A j k)) (congrArg _ (A k j))) (congrArg _ (d k))
 unfold Sheet.Atlas.passes; simp_rw [he]; exact and_congr Iff.rfl (iff_of_eq (congrArg (·∈_) (p.scopeH u i h)))
lemma resolve (i:A.Hcols)(h: Peel.stem (own A R i) 3 ⊆ S): stationT H (fU x) i ↔ stationT H (fU y) i:=by
 let V(i':ℕ)(p:i' ≤ 3):= (stem_mid (own A R i) p |>.trans h)
 refine and_congr (and_congr (p.scopeP u i (V 2 (by norm_num))) ?_) ?_; · apply forall_congr'; intro k; let v:= hop i.2 k 1; have he:= p.gives u (i.1,v) (fun y vv=> h (stem_join (r:=1) (t:=2) (step1 i k) vv)); have hm:= p.gives u i (V 2 (by norm_num)); dsimp only at he; change group.chord (H.T.give H.y (tower H (fU x) i.1) i.2 _ * tower H (fU x) i.1 (i.2,k) * (H.T.give H.y (tower H (fU x) i.1) v _)⁻¹) ≤ sigmaN H.y ↔ group.chord (H.T.give H.y (tower H (fU y) i.1) i.2 _*tower H (fU y) i.1 (i.2,k)*(H.T.give H.y (tower H (fU y) i.1) v _)⁻¹) ≤ sigmaN H.y; rw [he,hm,p.scope u i (V 1 (by norm_num)) k]
 apply iff_congr ((p.controls i (h (stem_home ..))).1); exact iff_of_eq (congrArg (checked A H.κ H.y i) (p.supreme u.hearth u.size _ (V 1 (by norm_num)))) -- tune
end Along
section meas
variable (H)
lemma station_meas (i:A.Hcols): MeasurableSet {x| stationT H x i}:=by
 let U(x:mState N A):= tower H x i.1; have ht:Measurable U:= (cont_horizontal _).measurable.comp (f:=fun x=>crownT H x) ((A.atmospheric_meas).comp H.skyio_m); let v:BPress.Sheet.Atlas:= H.T; let y:= H.y; refine askC (fun i:mState N A=>i.1) measurable_fst (fun a x=> TagGoal A H.T H.y (crownT H x) a.2 i ∧ destiny A H.κ H.y H.F a.1 x.2.1 i) ?_
 intro a; unfold TagGoal destiny; dsimp only; rw [Set.setOf_and,Set.setOf_and,Set.setOf_forall]; refine ((ht (H.T.passes_meas ..)).inter (MeasurableSet.iInter fun j=>?_ )).inter (?_ ); · let b:= fun i:A.Hcols=> a.2 i; exact measurableSet_le (group.continuous_chord.measurable.comp ((((v.give_meas y _ _|>.comp ht).mul ((measurable_pi_apply (i.2,j)).comp ht)).mul ((v.give_meas y _ _|>.comp ht).inv)))) measurable_const -- tune
 have he:= pick_eq A H.κ H.y; have h : MeasurableSet {x:mState N A| checked A H.κ H.y i (bodyBase A H.y H.F a.1 x.2.1 i)}:= by
    let f:=fun x:mState N A=>bodyBase A H.y H.F a.1 x.2.1 i; have hv:Measurable f:=(measurable_pi_apply _).comp ((body_meas A H.y H.F a.1).comp (measurable_fst.comp measurable_snd)); unfold checked; rw [Set.setOf_exists]; apply MeasurableSet.iUnion; intro i; exact measurableSet_lt measurable_const ((chord.cont (G:=group)).measurable.comp (f:=fun x=>(f x i,bMag B.D H.y i)) (((measurable_pi_apply i).comp hv).prodMk measurable_const))
 by_cases f:i∈ a.1; simpa only [f,true_iff] using h; simp only [f,false_iff]; exact h.compl
lemma casting (x:mState N A):holdsT A H.T H.y H.κ H.F x.1 x.2.1 ↔ ∀ i:A.Hcols, stationT H x i:=by
 let v:=A.atmospheric (skyio H x); let i:=x.1.1; let b:=x.1.2; unfold holdsT; rw [light_eq,awake]; exact and_comm.trans forall_and.symm -- tune

def submitted (Q:Seal (BlockY A R))(x: Choir A R):Prop:= ∀ i:A.Hcols, own A R i∈ petal Q 4 → stationT H (fU x) i
lemma submit_meas (h:Fast H.y)(V:Seal (BlockY A R)):MeasurableSet {x|submitted H V x}:=by
 unfold submitted; rw [Set.setOf_forall]; apply MeasurableSet.iInter; intro i; by_cases p:own A R i∈petal V 4; simp_rw [p,true_imp_iff]; exact (recipe A R h).measurable (station_meas ..); simp [p]
end meas
lemma judgment (u:Host R H)(x:Choir A R): holdsT A H.T H.y H.κ H.F (fU x).1 (fU x).2.1 ↔ ∀ Q∈ Camp x H, submitted H Q x:=by
 constructor; exact fun p _ _ i _=> (casting H _).1 p _; intro P; refine (casting ..).2 fun i=>?_ ; by_cases g:own A R i ∈ petal (Place H x) 4; obtain ⟨z,h,r⟩:= mem_biUnion.mp g; obtain ⟨a,f,h⟩:= mem_biUnion.mp (show z ∈ (Camp x H).biUnion id from (reconstruct fan _).symm ▸ h); exact P _ f i (mem_biUnion.mpr ⟨z,h,r⟩); exact u.settles x i g
lemma submittedC (u:Host R H)(p: Along x y (Contour.station fan S)): submitted H S x ↔ submitted H S y:=by
 unfold submitted; refine forall_congr' fun i=> imp_congr_right fun b=> p.resolve u i (fun j t=>?_ ); obtain ⟨x,g,x'⟩:=mem_biUnion.mp b; refine mem_biUnion.mpr ⟨x,g,?_⟩; exact stem_bay _ _ (stem_mid _ (by norm_num [fixedR]:4+3≤fixedR) (stem_join x' t))
end YM.CF.BPress.Peel
