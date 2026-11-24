import YM.CF.BPress.Mosaic.Tag
/- lemma:B-contour measurable extension via visible projection. Requires sup even on all visits ($w i$ bounds on same realized states). Additional Palette.core-bearing candidate helper. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mosaic
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Crew RG.PathData Grid Honey Recipe Peel
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}
open Peel.Spine Ledger Push.AbsoluteSums Contour
variable {R:Hangar (More N)} {H:Crew A}
-- pack map to used visible $work$.
variable {w:SlotT A R→ℝ}{u: SlotT A R→Visit A R H→ℂ} (T:SlotT A R)
private def advert (E:Seal (BlockY A R)) (x:Choir A R) := (Visible fan T E, Law.rep (watches fan T E) x (Classical.arbitrary _))
private lemma adv (E:Seal (BlockY A R)): Measurable (advert T E):= measurable_const.prodMk ((Law.rep_joint _).comp (f:=fun x:Choir A R=> (x,(Classical.arbitrary _))) (measurable_id.prodMk measurable_const))
private lemma identity {x y:Visit A R H}(p:advert T (Place H x.val) x.val=advert T (Place H y.val) y.val): Peek H T x.val y.val:=by
 let w:=congrArg Prod.fst p; let Q:= Visible fan T (Place H x.val); let e:=watches fan T (Place H x.val); have he:e=watches fan T (Place H y.val):= congrArg (fun Q:Seal (Seal (_))=> T ∪ Q.biUnion (Contour.station fan)) w -- tune placeholder type Seal
 refine ⟨w,fun i h=>?_ ⟩; have ht:i∈e:=h; let η(S:SlotT A R)(x:Choir A R):= Law.rep S x (Classical.arbitrary _); have hu:η e x.val i=η _ y.val i:=congrFun (congrArg Prod.snd p) i; exact ((Law.rep_L e _ _ i ht).symm.trans hu).trans (Law.rep_L _ _ _ i (he ▸ ht)) -- tune Eq
set_option synthInstance.maxHeartbeats 180000 in
set_option maxHeartbeats 800000 in
private lemma project (h:Fast H.y)(a:ℝ)(p:0≤a)(f:Visit A R H→ℂ)(g: Measurable f)(v:∀ x,‖f x‖≤a)(q:∀ x y,Peek H T x.val y.val→f x=f y):∃ G:Seal (SlotT A R) × Choir A R → ℂ, (∀ i,‖G i‖ ≤ a) ∧ Measurable G ∧ ∀ x:Visit A R H, f x = G (advert T (Place H x.val) x.val):=by
 haveI:StandardBorelSpace (Seal (SlotT A R) × Choir A R):=inferInstance; haveI:MeasurableSingletonClass (Choir A R):=inferInstance;  haveI: MeasurableSpace.CountablyGenerated (Seal (SlotT A R) × Choir A R):= inferInstance; haveI hm:MeasurableSpace.CountablySeparated (Seal (SlotT A R) × Choir A R):=inferInstance; haveI:StandardBorelSpace (Visit A R H):=visit_p h
 obtain ⟨G,p,v⟩:= Primary.Extensor.expend (fun x:Visit A R H=>advert T (Place H x.val) x.val) f a p ((askM (Place H) opt_m (advert T) (adv T)).comp measurable_subtype_coe) g v (fun i j u=> q i j (identity T u))
 exact ⟨G,p.1,p.2,v⟩
namespace Lift
-- Seal label always Grove. pad zeros. Use Reaches.
private def pack(w:SlotT A R→ℝ)(T:SlotT A R) : SlotT A R:=if w T=0 then {Classical.arbitrary _} else T
variable {f: Visit A R H→ℂ}{b:ℝ}
theorem setup (p: Lift b f)(h:Fast H.y): ∃ (T: SlotT A R→ SlotT A R)(u:SlotT A R→ SlotT A R→Choir A R→ℂ) (w:SlotT A R→ℝ), Cash T w 4 b ∧ Palmer.evenT (shape A R) T ∧ Reaches (Z:=fan) (T:=T) w u ∧ ∀ x:Visit A R H, ∑ i,u (Place H x.val) i x.val=f x:=by
 obtain ⟨w,v,u,hV⟩:=p.wraps; let T:=pack w
 have he(i:SlotT A R)(x y:Visit A R H)(t:Peek H (T i) x.val y.val): v i x=v i y:= by
    unfold T pack at t; split at t
    next h=> exact ((norm_le_zero_iff.mp (show ‖v i x‖ ≤0 from (h ▸ u.shore i x)))).trans ((norm_le_zero_iff.mp (h ▸ u.shore i y)).symm)
    next h=> exact u.reads i _ _ t
 choose! G Q P K using fun i=>project (T i) h (w i) (u.worth.pos _) (v i) (u.meas _) (u.shore i) (he i)
 let W(E:Seal (BlockY A R))(i:SlotT A R):=G i ∘ advert (T i) E; refine ⟨T,W,w,?_, ?_, ?_,?_⟩; · refine ⟨u.worth.pos,fun x=>?_⟩; convert u.worth.hits x using 1; ext i; by_cases h:w i=0; simp [Ledger.score,h,T,pack]; simp [Ledger.score,h,T,pack]
 · intro i; unfold T pack; split; exact Grove.single _; exact u.glow i ‹_›
 · refine ⟨fun i j=> (P _).comp (adv ..), fun i E S t=>?_,fun E i x y p=>?_ ,fun E i x=>Q i _ ⟩; · funext x; unfold W advert watches; rw [t]
   apply congrArg (G i); let U:=watches fan (T i) E; refine Prod.ext rfl (show Law.rep U x _=Law.rep U y _ from funext fun i=>?_); unfold Law.rep; split; exact p i ‹_›; rfl
 intro x; rw [hV]; exact sum_congr rfl fun i _=> (K i x).symm -- tune order
end Lift
end YM.CF.BPress.Mosaic
