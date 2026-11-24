import YM.CF.BPress.Peel.Palm
/-! Horizon settlement tests. No dependence on spin or analyzer for frames.Comparison.True. -/
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
variable {H: Crew A} {t T S E P: Seal (BlockY A R)}{i : BlockY A R}{x y: Choir A R}
abbrev crownT (H:Crew A) (v:mState N A): Micro (More N):= A.atmospheric (H.skyio v)
abbrev tower(H:Crew A)(x: mState N A)(i:A.Index):= Hazel.Letters.window A (crownT H x) i
def stationT(H:Crew A)(v:mState N A)(i:A.Hcols):Prop:= TagGoal A H.T H.y (crownT H v) v.1.2 i∧ destiny A H.κ H.y H.F v.1.1 v.2.1 i
lemma skyline_t (H:Crew A)(v:mState N A)(i: A.Index):tower H v i= Hazel.Letters.window A (H.port v) i:=by
 let k:=H.skyio v; let Y:=H.port v; have he(x:A.Air) : (A.atmospheric k) (A.skylink x)=Y (A.skylink x):= (A.mat_atm _ _).trans ((show Mission A H.y (H.skyio v) v.2.2.1 (H.port v) from marches ..).lens x |>.symm); -- tune ht marches explicit
 funext x; unfold tower window; rw [show crownT H v=A.atmospheric k from rfl,horizonDepth]; refine ((show Mission A H.y (H.skyio v) v.2.2.1 (H.port v) from marches ..).lens ((i,x.1), (⟨B.D-1,Nat.sub_one_lt B.D_pos.ne'⟩,x.2)) |>.symm).trans ?_ -- tune
 unfold Bands.skylink; dsimp only; rw [Nat.sub_add_cancel B.D_pos]; rfl
lemma step1 (v:A.Hcols)(i:SpatialDir): own A R (v.1,hop v.2 i 1)∈Peel.stem (own A R v) 1:= Peel.radial v _ ((column_eq).2 ⟨rfl, delta_hop ..⟩) R.L.property
private lemma neutral (q:A.Hcols) {x:Choir A R}(p: own A R q∉ Place H x): (fU x).1.2 q=0:=by
 let i:=own A R q; have ht:x i∈ brisk (B:=B) R H.y:= Classical.byContradiction fun h=>p (mem_filter.mpr ⟨mem_univ _,h⟩); exact (brisk_eq ..|>.1 ht).2 _
lemma settle (x: Choir A R)(i:A.Hcols)(Q: Summer A H.F H.P.upper (H.P.low H.y) (H.P.reach H.y) (H.P.chunks H.y))(p:H.P.reach H.y≤R.L.val){a C D:ℝ}(V:Plenty H.T H.P B D H.κ C a H.y)(u:own A R i∉ petal (Place H x) 4) : stationT H (fU x) i:=by
 let Bv:= Place H x; let bv:=debts H x; have hu: Good A R bv 4 i:=fun v=> u (mem_biUnion.mpr (let ⟨a,b,c⟩:= mem_biUnion.mp (at_petal.mpr v); ⟨a,fat_m x b,c⟩)) -- Exists let elimination
 have ht : x=x:=rfl; let v:= fU x
 have hT(j: A.Hcols)(h:Good A R bv 2 j): Atlas.Heals 1 H.y (tower H v j.1) j.2:=by rw [skyline_t]; exact Reserve.healed V Q p H.Z _ _ h -- tune bv binder
 refine ⟨⟨(V.heals _ _ _ (hT i (good_m hu (by norm_num)))).pass, ?_⟩, ?_ ⟩
 · intro k; let j:A.Hcols:= (i.1,hop i.2 k 1); have he(j: A.Hcols) (t:own A R j∈Peel.stem (own A R i) 1) : (fU x).1.2 j=0:= neutral j (fun f=> u (mem_biUnion.mpr ⟨own A R j,f, stem_mid _ (by norm_num : 1≤4) (stem_flip t)⟩)); have h:Good A R bv 2 j:= good_cc (good_m hu (by norm_num : 2+1≤4)) rfl ((delta_hop i.2 k 1).trans R.L.property)
   exact (V.bonds _ (tower H v i.1) (i.2,k) (hT i (good_m hu (by norm_num))) (hT j h) _ _).2 ((he i (stem_home ..)).trans (he j (step1 i k)).symm) -- tune defeq hop vs flat
 refine (CheckWind.open_gate V.wind.choose_spec Q v.1.1 v.2.1 i (fun t l=>?_)).2.2; obtain ⟨a,b⟩:= column_eq.mp l; exact Reserve.cool (v:=v.2.1) (good_cc (good_m hu (by norm_num :0+1 ≤4)) a.symm (b.trans p))
structure Host (R:Hangar (More N))(H:Crew A) :Prop where
 hearth : summerCo H
 size: H.P.reach H.y≤R.L.val
 settles (x: Choir A R)(i:A.Hcols): own A R i ∉ petal (Place H x) 4 → stationT H (fU x) i
lemma hosting (Q: Summer A H.F H.P.upper (H.P.low H.y) (H.P.reach H.y) (H.P.chunks H.y))(p:H.P.reach H.y≤R.L.val){a C D:ℝ}(V:Plenty H.T H.P B D H.κ C a H.y) : Host R H:= ⟨Q.seen,p,fun i v=> settle i v Q p V⟩
end YM.CF.BPress.Peel
