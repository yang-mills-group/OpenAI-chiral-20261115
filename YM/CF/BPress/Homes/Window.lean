import YM.CF.BPress.Homes.Criteria
import YM.CF.BPress.Habitat.Mascot
/-!
 Put the measurability checks on the implemented pricing domain. The Pass
 tests ensure the uniform inverses are of continuous data (outside this set
 we don't use continuity of a totalized inverse).
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
namespace YM.CF.BPress.Homes
open Function NormedSpace Metric Finset Lattice Fock Spin Pf Thera Cellar Cellar.Pass Spin.Trans MeasureTheory
open Spin.Paint Spin.Stride Habitat Habitat.Upled Habitat.Plain Habitat.Driver Nacre Laic Font Tulip Tenant Branch SU Cube Lat Dial Scroll
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff InnerProductSpace Classical YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {D:Type}[TopologicalSpace D][MeasurableSpace D][OpensMeasurableSpace D]{N:Side}{U:Driver N}{A B W:Pledge}

lemma transfer (q p:D→ Prop)(v:MeasurableSet {x| p x})(h:MeasurableSet {x: {x:D// p x}| q x.val})(g:∀ i,q i→ p i): MeasurableSet {x|q x}:=by
 rw [show {x|q x}= Subtype.val '' {x:{x:D// p x}|q x.val} from ?_]; exact (MeasurableEmbedding.subtype_coe v).measurableSet_image.mpr h
 ext1 x; constructor; · intro p; exact ⟨⟨x,g x p⟩,p,rfl⟩
 rintro ⟨i,x,rfl⟩; exact x
lemma closedPlan (F:D→Paint (More N))(p:Continuous F) : IsClosed {x:D| MatPlan (F x)}:=by
 unfold MatPlan; rw [Set.setOf_forall]; apply isClosed_iInter; intro i; let f(x):=F x i; have hp:Continuous f:=(continuous_apply i).comp p; change IsClosed {x|Spin.Sym (f x)}; simp_rw [show ∀ (A:Op Slot), Spin.Sym A↔ Aᵀ=A∧ A∈unitary (Op Slot)∧A.det=1 from fun A=> ⟨fun h=>⟨h.triangle,h.gate,h.traceX⟩,fun ⟨p,q,r⟩=>⟨p,q,r⟩⟩, Set.setOf_and]; exact (isClosed_eq hp.matrix_transpose hp).inter (((isClosed_eq (hp.star.mul hp) continuous_const).inter (isClosed_eq (hp.mul hp.star) continuous_const) : IsClosed {x| f x∈ unitary (Op Slot)}).inter (isClosed_eq hp.matrix_det continuous_const))

variable (U)
private abbrev Skyl := {x:Plain N// Guard x.G U.d}
private abbrev sA (x:Skyl U) := U.packsA x.val.G
private abbrev sT (x: Skyl U):= U.packsM x.val.G
private abbrev kP (i:Bool)(x:Skyl U):= cutM (Stride.Locks x.val.key i)
private abbrev lo (x: Skyl U):= 1-(kP U true x+kP U false x)
private lemma to_cell (x:Skyl U): Empties (kP U true x) (kP U false x) (lo U x):=by
 let P:=Hole.plusMinus x.val.key; exact ⟨P.p,P.q,rfl,P.orth⟩
private lemma board (x: Skyl U): PairBoard (kP U true x) (kP U false x) (lo U x) (U.model.col x.val 2):=⟨to_cell U x,cut_real _,cut_real _,(Hole.coupling_lock (Plain.spin x.val false 2) _).symm,(Hole.coupling_lock (Plain.spin x.val false 2) _).symm⟩ -- tune
omit [MeasurableSpace D] [OpensMeasurableSpace D] in lemma duty(openForm:Spin.Form N D)(f:D→Op (Single N))(t:openForm.Comes A f): Continuous f:=by obtain ⟨u,w,q,L,h⟩:=t; exact (continuous_finsetSum (f:=fun i y=>u i y) Finset.univ (fun i h=>(q i).cont)).congr (fun x=> (h x).symm)
private abbrev g5 (x:Skyl U):OpenW N U.d:=⟨x.val.G,x.property⟩
set_option maxHeartbeats 50000 in
private lemma g_up : Continuous (g5 U) := Continuous.subtype_mk (Plain.cont_G.comp continuous_subtype_val) _
set_option maxHeartbeats 50000 in
private lemma pA_up (V:U.Wish A B W) : Continuous fun x : OpenW N U.d=> U.packsA x.val:=
 duty (A:=A) (AtW N U.d) (fun i=> U.packsA i.val) (V.pen.entries U.M)
set_option maxHeartbeats 50000 in
private lemma pT_up (V:U.Wish A B W) : Continuous fun x:OpenW N U.d=> U.packsM x.val:=
 duty (A:=priceS A B W) (AtW N U.d) (fun i=> U.packsM i.val) (CostS U.M (P:=A) (Q:=B) (W:=W) V.pen U.F V.pay)
set_option maxHeartbeats 50000 in
private lemma raw_up (V:U.Wish A B W) : Continuous (sA U)∧ Continuous (sT U):=
 by
 let f(x:OpenW N U.d):= U.packsA x.val
 let l(x: OpenW N U.d):=U.packsM x.val
 rw [show sA U=f ∘ g5 U from rfl,show sT U=l ∘ g5 U from rfl]
 exact ⟨(pA_up U V).comp (g_up U),(pT_up U V).comp (g_up U)⟩
private lemma k_up(i:Bool): Continuous (kP U i):=by
 haveI : DiscreteTopology (Fate N):= inferInstance
 let f(x:Fate N):= cutM (Locks (univ.filter (fun i=>x i)) i); have h:Continuous f:=continuous_of_discreteTopology; exact h.comp (Plain.cont_star.comp continuous_subtype_val)
private lemma lo_up : Continuous (lo U):=continuous_const.sub ((k_up U true).add (k_up U false))
private abbrev mA (x:Skyl U):= Pf.mood (sA U x) (sT U x)
private abbrev trust (x:Skyl U) : Prop:=Pass (kP U true x) (kP U false x) (lo U x) (mA U x) U.ε
private lemma sky_proj (V:Wish U A B W) (x:Skyl U): IsStarProjection (sA U x):=V.pen.proj U.M ⟨x.val.G,x.property⟩
private lemma sky_tag (V:Wish U A B W) (x:Skyl U) : TagG (sA U x) (sT U x):= tag_g _ (sky_proj U V x)
private lemma up_tilt (V:Wish U A B W)(t:ℝ): Continuous fun x=> tilt (sA U x) (sT U x) t:= tilt_f (raw_up U V).1 (raw_up U V).2 (sky_proj U V) (sky_tag U V) t
private lemma trust_f (V:U.Wish A B W): IsClosed {x|trust U x}:= pass_f (up_tilt U V (1:ℝ)) (k_up U true) (k_up U false) (lo_up U) (to_cell U) _
private abbrev Rain := {x: Skyl U // trust U x}
local instance : OpensMeasurableSpace (Plain N) := @BorelSpace.opensMeasurable _ _ _ (Plain.bore_p (N:=N)) -- only local avoid divergent creations.
private abbrev k0 (u:Rain U): Plain N:= u.val.val
-- path and projector bookmarks for $Issued$ test
private abbrev round (v:ℝ)(p:Rain U):= traceM (Locks (k0 U p).key true) (Locks (k0 U p).key false) (sA U p.val) (sT U p.val) v
private lemma round_c (V:Wish U A B W)(i:ℝ)(p:i∈Set.Icc (0:ℝ) 1): Continuous (round U i):=by
 let w:= kP U; let T' : Rain U→ Skyl U:=Subtype.val; let F(p:Rain U):=Pf.mood (sA U p.val) (sT U p.val)
 have hk:Continuous F:=(up_tilt U V 1).comp continuous_subtype_val
 have hv:= smooth_f (s:=hk) (P:=kP U true ∘ T') (Q:=kP U false ∘ T') (L:= lo U ∘ T') ((k_up U true).comp continuous_subtype_val) ((k_up U false).comp continuous_subtype_val) ((lo_up U).comp continuous_subtype_val) (ε:=U.ε) (fun i=> i.property) i (tiny_t p)
 rw [show round U i= (fun x:Rain U=> smoothP ((kP U true ∘ T') x) ((kP U false ∘ T') x) ((lo U ∘ T') x) (F x) i) from rfl]; exact hv
private abbrev pathI (b:Bool) (x:Rain U)(t:ℝ):= Paint.coupling (Plain.spin (k0 U x) b t)
private lemma cam : Continuous (k0 U):= continuous_subtype_val.comp continuous_subtype_val
private lemma cont_path (b:Bool) : Continuous (uncurry (pathI U b)) := Paint.coupling_cont.comp ((Plain.cont_spin b).comp (f:=fun u:Rain U × ℝ => (k0 U u.1,u.2)) (((cam U).comp continuous_fst).prodMk continuous_snd))

-- Pack rest
private abbrev faces (x:Rain U):=∀ t∈Set.Icc (0:ℝ) 1, Bore (tilt (sA U x.val) (sT U x.val) t) (pathI U false x 0) U.v
private lemma tileT (V:U.Wish A B W)(t:ℝ): Continuous fun x:Rain U=> tilt (sA U x.val) (sT U x.val) t:=by
 let i := (fun x:Rain U=> x.val); change Continuous (fun x:Rain U=> tilt _ _ _); have hv:= (up_tilt U V t).comp (f:=i) continuous_subtype_val; exact hv
private lemma faces_f (V:U.Wish A B W) : IsClosed {x|faces U x}:=by unfold faces; simp_rw [Set.setOf_forall]; exact isClosed_iInter fun i=> isClosed_iInter fun _=> bore_p (tileT U V i) ((cont_path U false).uncurry_right 0) _
private abbrev ribs (x:Rain U):=∀ t∈Set.Icc (0:ℝ) 1, Bore (mA U x.val) (pathI U false x t) U.v ∧ Bore (round U t x) (pathI U false x 1) U.v
private lemma ribs_c (V:U.Wish A B W) : IsClosed {x| ribs U x} := by
 unfold ribs; simp_rw [Set.setOf_forall,Set.setOf_and]
 refine isClosed_iInter fun i=> isClosed_iInter fun p=> ?_; exact (bore_p (tileT U V (1:ℝ)) ((cont_path U false).uncurry_right i) U.v).inter (bore_p (round_c U V i p) ((cont_path U false).uncurry_right 1) U.v) -- tune
private abbrev lampL (x:Rain U):=∀ t∈Set.Icc (1:ℝ) 2, Bore (round U 0 x) (pathI U false x t) U.v
private lemma lamp_c (V:U.Wish A B W): IsClosed {x | lampL U x}:= by unfold lampL; simp_rw [Set.setOf_forall]; exact isClosed_iInter fun i=> isClosed_iInter fun _=> bore_p (round_c U V 0 (by norm_num)) ((cont_path U false).uncurry_right i) U.v
private abbrev fieldT (x: Plain N):=Issued (U.model.keys true x) (U.model.keys false x) (U.model.A x) (U.model.M x) (U.model.col x) (U.model.col' x) U.v U.ε
private lemma lease_f (V:U.Wish A B W) : MeasurableSet {x:Rain U | fieldT U (k0 U x)}:=by
 have h(x): fieldT U (k0 U x)↔ faces U x∧ribs U x∧lampL U x∧‖sT U x.val‖≤1∧ (∀ i ∈ Set.Icc (0:ℝ) 2,HasDerivAt (pathI U false x) (pathI U true x i) i):= by
    refine ⟨fun h=>⟨h.front,(fun i p=>⟨h.center i p,h.warp i p⟩),h.back,h.near,h.diff⟩, fun ⟨f,v,t,u,H⟩=>?_⟩; exact ⟨sky_proj U V _,sky_tag U V _,u,x.property,outage _,board U _,((cont_path U true).uncurry_left x).continuousOn, H,f,(fun i p=>(v i p).1),(fun i p=>(v i p).2),t⟩
 simp_rw [h,Set.setOf_and]
 have ht: Continuous (fun x:Rain U=> sT U x.val) := (raw_up U V).2.comp continuous_subtype_val
 letI : FirstCountableTopology (Lamp (More N)):= inferInstance
 letI : FirstCountableTopology (Plain N):= inferInstance
 letI : FirstCountableTopology (Skyl U):= TopologicalSpace.Subtype.firstCountableTopology (α:=Plain N) _
 letI : FirstCountableTopology (Rain U):= TopologicalSpace.Subtype.firstCountableTopology (α:=Skyl U) _
 refine (faces_f U V).measurableSet.inter ((ribs_c U V).measurableSet.inter ((lamp_c U V).measurableSet.inter ((isClosed_le ht.norm continuous_const).measurableSet.inter (allHours (cont_path U false) (cont_path U true)))))
private lemma sk_meas(V:Wish U A B W) : MeasurableSet {x:Skyl U | U.Hallowed x.val}:=by
 have hp : MeasurableSet {x:Skyl U|fieldT U x.val}:= transfer _ (trust U) (trust_f U V).measurableSet (lease_f U V) (fun x u=>u.rails)
 have hu(x:Skyl U): U.Hallowed x.val↔ Slow x.val.G (hook x.val.X) U.p ∧ MatPlan (U.model.KG x.val) ∧ (∀ t∈Set.Icc (0:ℝ) 2,∀ z:Site (More N),∀ a:Bool, ‖x.val.spin a t z‖≤ U.h) ∧ fieldT U x.val:= ⟨fun p=>⟨p.tuneK,p.day,p.toll,p.state⟩, fun ⟨p,l,v,f⟩=>⟨x.property,p,v,f,l⟩⟩
 simp_rw [hu,Set.setOf_and]; have hc (b:Bool)(t:ℝ): Continuous fun x:Skyl U=> Plain.spin x.val b t := (Plain.cont_spin b).comp (continuous_subtype_val.prodMk continuous_const)
 refine MeasurableSet.inter ?_ ((closedPlan (fun x:Skyl U=> U.model.KG x.val) (hc false _)).measurableSet.inter (MeasurableSet.inter ?_ hp)); swap
 · simp_rw [Set.setOf_forall]; exact (isClosed_iInter (fun i=>isClosed_iInter (fun _=>isClosed_iInter (fun p =>isClosed_iInter (fun h=>isClosed_le (((continuous_apply p).comp (hc h i)).norm) continuous_const))))).measurableSet
 unfold Slow; rw [Set.setOf_forall]; refine MeasurableSet.iInter (fun i=>?_); rw [Set.setOf_forall]; refine MeasurableSet.iInter (fun j=>?_)
 let F(p:Skyl U):= p.val.G (i,j); let Vct(v:Site (More N))(p:Skyl U):= hook p.val.X v
 have ht:Continuous F:=(continuous_apply _).comp (Plain.cont_G.comp continuous_subtype_val); have he(v):Continuous (Vct v):= continuous_subtype_val.comp ((continuous_apply v).comp (Plain.cont_X.comp continuous_subtype_val))
 exact (isOpen_lt (((turn_cont.comp (f:=fun p=>(F p,Vct (i+step j) p)) (ht.prodMk (he _))).sub (he i)).norm) continuous_const).measurableSet
lemma domain (V:Wish U A B W): StandardBorelSpace U.Pose:=by
 letI : CompleteSpace (Upled Slot):=inferInstance
 letI : SecondCountableTopology (Upled Slot):=inferInstance
 letI : PolishSpace (Upled Slot):=inferInstance
 letI : BorelSpace (Upled Slot):=inferInstance
 letI : StandardBorelSpace (Upled Slot) := inferInstance
 letI : StandardBorelSpace (Lamp (More N)) := StandardBorelSpace.pi_countable (α:=fun _:Site (More N)=> Upled Slot)
 letI : StandardBorelSpace (Stun N) := inferInstance
 letI : StandardBorelSpace (Fate N) := inferInstance
 letI : StandardBorelSpace (Plain N):= inferInstance
 apply MeasurableSet.standardBorel (s:={x:Plain N| U.Hallowed x})
 exact transfer _ _ ((Phase.cover_closed (More N) U.d).preimage Plain.cont_G).measurableSet (sk_meas U V) (fun x u=>u.glow)
end YM.CF.BPress.Homes
#print axioms YM.CF.BPress.Homes.domain
