import YM.CF.BPress.Huon.Caster
/- Borel assembly. compose with Producer.Restr.When no world.$erg=0`. Price.rates can be imposed outside submitted.OnCore compare. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along Contour
variable {m s N:Side}{B:BandWidth}{A:Bands (More N) B}{R:Hangar (More N)}
variable {H:Sugar.Crew A}{X:Sugar.Stage N}{Y:Driver N}
abbrev passV (H:Sugar.Crew A)(Q:SlotT A R):Set (Choir A R) := {x| Peel.points A R H x ∧ Q∈Camp x H}
private lemma cm (Q:SlotT A R): MeasurableSet {x| Q∈Camp x H}:= opt_m (H:=H) (show MeasurableSet {x|Q∈ Palmer.Parts Peel.fan x} from (Set.to_countable _).measurableSet)
lemma passM (v: House.Fast H.y)(T:SlotT A R) : MeasurableSet (passV H T):= ((recipe A R v).measurable H.Role_meas).inter (cm _)
lemma ice_m(A:Bands (More N) B)(R:Hangar (More N))(p:SlotT A R): Measurable (fun x=>ice x p):= by
 apply bucketM (t:=own A R); · exact (measurable_of_countable (fun x:BlockY A R → Bank R=>(beset A R x).1)).comp (show Measurable (icon A R) from measurable_pi_lambda _ (fun i=>(measurable_fst.comp (measurable_pi_apply i))))
 exact measurable_const
lemma ice_eq00 (x y: Choir A R)(g:SlotT A R)(u:Peel.Along x y g) : ice x g= ice y g:=by ext j; simp only [ice,chipAt,mem_filter]; exact and_congr_left fun v=> (u.controls j v).1
-- Core.ext
structure PaidQ (T:SlotT A R)(X:Rates)(H:Sugar.Crew A)(F:Visit A R H→ℂ)(f: Choir A R →ℂ):Prop where
 env : Envelope f
 scout: ScopedB f (Contour.station Peel.fan T)
 budget(x): ‖f x‖ ≤ Real.exp (X.budgetP H T x)
 wake(x): f x≠0→ submitted H T x ∧ Rates.admits H T x
 lands (x: Visit A R H)(h:T∈Camp x.val H): f x.val=F x
lemma admit_m (T:SlotT A R): MeasurableSet {x| Rates.admits H T x}:=by
 let W:= fun x=> Upper H x T; refine askC (fun x=> W x) (upper_m ..) (fun S x=> ∀ i∈ S,∃ j:Fin 5, j≠0∧ (x i).1=House.background R j) ?_ ; intro S
 simp only [Set.setOf_forall]; apply MeasurableSet.iInter; intro i; by_cases t:i∈ S; swap; · simp [t]
 let P(x: Realm B N R):Prop:=∃ j:Fin 5,j≠0∧ x.1=House.background R j; have he: MeasurableSet {x|P x}:=measurable_fst ((Set.to_countable {x:Bank R| ∃ j:Fin 5,j≠0∧ x=House.background R j}).measurableSet) ; simp only [t, Set.iInter_const]; exact measurable_pi_apply (X:=fun _=>Realm B N R) i he
set_option maxHeartbeats 800000 in
lemma Budget_open (K:Rates)(T:SlotT A R): Measurable (Rates.budgetP H K T):= by
 have V:Measurable fun x:Choir A R=> ((Upper H x T).card:ℝ):= (measurable_of_countable (fun x:SlotT A R=>(x.card:ℝ))).comp (upper_m H T); have h:Measurable fun x: Choir A R=> ((debris H x T).card:ℝ):=(measurable_of_countable (fun x:SlotT A R=>(x.card:ℝ))).comp (debris_m H T); have t:Measurable fun x: Choir A R=> ((ice x T).card:ℝ):= (measurable_of_countable (fun x:Finset A.Hcols=>(x.card:ℝ))).comp (ice_m A R T); unfold Rates.budgetP; exact ((measurable_const.mul V).neg.add (measurable_const.mul h)).sub (measurable_const.mul t)
lemma cores (T:SlotT A R)(K:Rates)(G:Visit A R H→ℂ)(p:Measurable G)(h:Fast H.y) (V:Host R H)
    (u:∀ x:Visit A R H,T∈Camp x.val H→ ‖G x‖≤ Real.exp (K.budgetP H T x.val) ∧ Rates.admits H T x.val)
    (t:∀ x y:Visit A R H, T∈Camp x.val H → T∈Camp y.val H→ Peel.Along x.val y.val (Contour.station Peel.fan T)→ G x=G y):∃ f, PaidQ T K H G f:=by
 let S:=Contour.station Peel.fan T; let Δ:=passV H T; let U(x:Δ):Visit A R H:= ⟨x.val,x.property.1⟩; let c:= Rates.budgetP H K T; let P(x:Choir A R):= Law.rep S x (Classical.arbitrary _); have hp(x):Peel.Along x (P x) S:=fun i t=>(Law.rep_L S x _ i t).symm; have hk(x y:Choir A R)(u:Peel.Along x y S):P x=P y:=funext (fun i=>by unfold P Law.rep; split; exact u i ‹_›; rfl)
 have hm : Measurable P:= (Law.rep_joint _).comp (f:=fun x: Choir A R=> (x,(Classical.arbitrary _))) (measurable_id.prodMk measurable_const); haveI:StandardBorelSpace Δ:=(passM h T).standardBorel; -- Instance TC
 have he(x y: Choir A R)(v:Peel.Along x y S):c x=c y:=by obtain ⟨d,b⟩:= upper_loc (H:=H) (v.mono (fun _ g=> estate0 (T:=T) g)); unfold c Rates.budgetP; rw [b,d,ice_eq00 x y T (v.mono (fun _ u=>estate0 u))]
 have ht(x: Choir A R):Rates.admits H T x↔Rates.admits H T (P x):= by
    have u':= (hp x).mono (fun i w=> estate0 (T:=T) w); have hv:= (upper_loc (H:=H) u').2; unfold Rates.admits; apply forall_congr'; intro i; rw [←hv]; refine imp_congr_right fun z=>?_ ; rw [← u' i (sdiff_subset z)] -- unused (k)
 let b(x: Choir A R):Prop:= submitted H T (P x)∧ Rates.admits H T (P x); have hv:MeasurableSet {x|b x}:=hm ((submit_meas H h T).inter (admit_m _)); have hz(x:Visit A R H)(t:T∈ Camp x.val H): b x.val:= ⟨ (submittedC V (hp x.val)).1 ((Peel.judgment V x.val).1 x.property.2 T t), (ht x.val).1 ((u x t).2) ⟩
 have hc₁: ∀ i:Δ, ‖G (U i)‖ ≤ Real.exp (c (P i.val)):=fun i=>(u (U i) i.property.2).1.trans_eq (congrArg Real.exp (he i.val (P i.val) (hp i.val)))
 have hc₂(i j:Δ)(u: P i.val=P j.val) : G (U i)=G (U j):= t (U i) (U j) i.property.2 j.property.2 (fun l v=> Eq.trans (hp i.val l v) (Eq.trans (congrFun u l) (hp j.val l v).symm))
 obtain ⟨g,F,f,P'⟩:= Primary.Extensor.expendV (P ∘ (Subtype.val (p:=Membership.mem Δ))) (G ∘ U) (Real.exp ∘ c) (fun x=>(Real.exp_pos _).le) ((Budget_open K T).exp) (hm.comp measurable_subtype_coe) (p.comp (Measurable.subtype_mk measurable_subtype_coe)) hc₁ hc₂
 let φ(x):= if b x then g (P x) else 0; have hx(x:Choir A R) : ‖φ x‖ ≤ Real.exp (K.budgetP H T x):=by
    unfold φ; split; next b=> exact (F (P x)).trans_eq (congrArg Real.exp (he x (P x) (hp x)).symm)
                                                                                                                      -- tune
    next b=> simp only [norm_zero]; exact (Real.exp_pos _).le
 refine ⟨φ,⟨ Measurable.ite hv (f.comp hm) measurable_const, Real.exp (K.bad*T.card), fun x=>(hx x).trans (Real.exp_monotone ?_)⟩, fun x y v=>?_,hx, fun x t=>?_ ,fun x u=>?_⟩
 · apply le_trans _ (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (show (debris H x T).card ≤ _ from card_le_card inter_subset_right)) K.paid); unfold Rates.budgetP; have h:= K.earn; have he:=K.yellow; linarith [mul_nonneg he (Nat.cast_nonneg (ice x T).card (α:=ℝ)), mul_nonneg h (Nat.cast_nonneg (Upper H x T).card (α:=ℝ))] -- tune inter
 · unfold φ b; rw [hk x y v]
 · have h':b x:= Classical.byContradiction fun h=>t (if_neg h); exact ⟨(submittedC V (hp x)).2 h'.1,(ht x).2 h'.2⟩
 rw [show φ x.val=g (P x.val) from if_pos (hz x u)]; exact (P' (⟨x.val,x.property,u⟩: Δ)).symm
end YM.CF.BPress.Huon
