import YM.CF.BPress.Lilac.Pommel
/-! Label display after gauge fix. At all blocks further than 29 (≤ exact) from bad in tangential geometry, one uniform label. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Lilac
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Born Peel.Along
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
variable {H: Sugar.Crew A}{T:GramM N}{X: Sugar.Stage N}{Y:Driver N}{k r:ℕ}{e c d:ℝ}{i: SiteX A R}
namespace Stripe
-- $the first and second cases$ for short terms use this
abbrev vicinity(H: Sugar.Crew A)(x:Choir A R):= petal (debts H x) 29
def chip (x: Choir A R)(i:SiteX A R):= (fU x).1.2 (porch A R i (Classical.arbitrary _))
lemma chip_m (i:SiteX A R): Measurable (fun x:Choir A R=> chip x i):=by
 let o:=porch A R i (Classical.arbitrary (Patio R)); change Measurable fun x:Choir A R=> ( (x (own A R o)).1 (packB R o.2)).2; exact measurable_snd.comp ((measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply (own A R o)))) -- i' implicit tune
lemma vicinity_iff(x: Choir A R) : i∈ vicinity H x ↔ ∃ a∈ Peel.stem i 29,a∈debts H x:=by
 constructor; intro p; obtain ⟨i,p,t⟩:= mem_biUnion.mp p; exact ⟨i,stem_flip t,p⟩; rintro ⟨j,u,p⟩; exact mem_biUnion.mpr ⟨j,p,stem_flip u⟩
lemma vicinity_m(i:SiteX A R): MeasurableSet {x: Choir A R|i∈vicinity H x}:=by
 rw [show {x:Choir A R|_}= ⋃ a:SiteX A R, {x: Choir A R|a∈Peel.stem i 29∧ a∈debts H x} from ?_]; swap; · ext x; simp [vicinity_iff] -- tune
 apply MeasurableSet.iUnion; intro a; by_cases u:a∈ Peel.stem i 29; simp only [u,true_and]; simp_rw [debt_m]; exact measurable_pi_apply (X:=fun _=>Realm B N R) a (unholy_flag ..); simp [u]
lemma tag_in (x:Visit A R H)(j:A.Hcols) : (H.tape (fU x.val)).z j=(fU x.val).1.2 j:=congrFun (flash_code A _) j
lemma solidarity (x: Visit A R H)(v:i ∉ vicinity H x.val)(b:A.Hcols)(p:own A R b∈Peel.stem i 1):Good A R (debts H x.val) 6 b:=by
 intro e; obtain ⟨i,p',h⟩:= mem_biUnion.mp (at_petal.mpr e); exact v (mem_biUnion.mpr ⟨i,p',stem_mid i (by norm_num : 6+1 ≤29) (stem_join h (stem_flip p))⟩)
private lemma spanD (x y:A.Hcols)(g:own A R x=own A R y): delta x.2 y.2≤R.L.val:=by
 let L:= R.L; let Q:= R.period; apply delta_le.mpr; intro i; let a:=packB R x.2 i; let b:=packB R y.2 i; let U:= tang R y.2 i; have he(r:Fin L.val)(u: Tri (More N))(f:tang R u i=U)(t:r=packB R u i): u i= Radix.dial (More N) L Q 0 U r.val:= by rw [←f,t]; exact ((Radix.clock (More N) R.L R.period R.geom 0).apply_symm_apply (u i)).symm
 have ht(l k:Fin L.val)(p:l.val≤k.val): let f(n:ℕ):=Radix.dial (More N) L Q 0 U n; delta1 (More N) (f k.val) (f l.val) ≤ L.val:=by
    intro f; have he : f k.val=f l.val+ ↑(k.val-l.val):=by unfold f; rw [← dial_length, Nat.add_sub_of_le p] -- name tune
    rw [he]; exact (delta_nat ..).trans ((Nat.sub_le ..).trans k.isLt.le)
 change delta1 (More N) (x.2 i) (y.2 i) ≤_; rw [he a x.2 (congrFun (congrArg Prod.snd g) i) rfl]; -- danger dep rewriting Y on right? local notation used.
 let F:= Radix.dial (More N) L Q 0 U; have hk: y.2 i=F b.val:= he b y.2 rfl rfl; rcases le_total b a with p|p; rw [hk]; exact ht b a p; rw [d_sym, hk]; exact ht a b p
variable (F:Rented R H X d e k c)
local notation "φ"=> vicinity H
variable (x: Visit A R H) (v: i ∉ vicinity H x.val)
include v F
lemma steadyP (a:A.Hcols)(h:own A R a=i): (H.tape (fU x.val)).z a=chip x.val i:=by
 let p:= (F.pay _ x.property).licence.grip; let b:= porch A R i (Classical.arbitrary (Patio R)); have hu:own A R a=own A R b:=h.trans (porch_own ..).symm; refine (carriedP p.settle (good_m (solidarity x v a ?_) (by norm_num)) (show a.1=b.1 from congrArg (fun x:SiteX A R=>x.1) hu) (spanD a b hu)).trans (tag_in x b); exact h.symm ▸ stem_home ..
lemma ins (p:Patio R): let z:=chip x.val i; (x.val i).1 p=(false,z):=by
 intro z; let a:=porch A R i p; have ht: ¬ unholy R H.y (x.val i):= fun p=> v (petals (debt_m x.val|>.mpr p)); have hv:= steadyP F x v a (porch_own ..); rw [tag_in] at hv; change (gather A R (icon A R x.val) a).2=_ at hv; refine Prod.ext (Bool.eq_false_iff.mpr (fun h=> ht ⟨p,.inl h⟩)) ?_; rw [show (x.val i).1 p=gather A R (icon A R x.val) a from (gather_p A R (icon A R x.val) i p).symm]; exact hv
lemma grade_t : i∈ Peel.Place H x.val ↔ chip x.val i ≠0:=by
 let Y: Realm B N R:=x.val i; rw [Peel.Place,innings,mem_filter]; have ht:¬unholy R H.y Y:=fun p=>v (petals (debt_m x.val|>.2 p)); unfold Y at ht; simp only [mem_univ,true_and, House.excite,brisk_eq,ht,not_false_eq_true]; simp_rw [ins F x v]; simp [ht] -- tune implicit
omit F
lemma visits_t {t:Seal (SiteX A R)}(y: Visit A R H)(h:Peek H t x.val y.val)(p: Peel.stem i 29 ⊆ t) : i ∉ vicinity H y.val∧ chip x.val i=chip y.val i:=by
 let k:=Classical.arbitrary (Patio R); let a:=porch A R i k; have ht:= h.run.mono (show t ⊆ Contour.watches Peel.fan t (Peel.Place H x.val) from subset_union_left); refine ⟨fun v'=> v (at_petal.mpr (((ht.masks (H:=H) p)).2 (at_petal.mp v'))), (ht.controls a ?_).2.1⟩; exact p ((porch_own ..).symm ▸ stem_home ..) -- tune ht direction
end Stripe
end YM.CF.BPress.Lilac
