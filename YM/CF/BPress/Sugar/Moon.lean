import YM.CF.BPress.Sugar.Stan
/-! measurability museum (ii). -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Sugar.Crew
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Stage Net Bands Meadow.Frame Lute
variable {N: Side}{B:BandWidth}{A:Bands (More N) B}(X:Stage N)(R:Hangar (More N))(H:Crew A)
local notation "η"=> mState N A
abbrev duoR (x:mState N A)(i:A.Index) : Micro (More N)× Duo (More N):= (H.port x,A.putF H.T H.y (H.port x) i (layout (A:=A) x i))
lemma duoR_M (i:A.Index): Measurable fun x=>H.duoR x i :=by have hm:= ((measurable_pi_apply i).comp (layoutP (A:=A))); exact H.port_m.prodMk (askM (fun p:η=>layout p i) hm (fun j x=> A.putF H.T H.y (H.port x) i j) (fun j=> (A.putF_meas ..).comp H.port_m)) -- tune
lemma cones_m (i:A.Hcols): Measurable fun x=>(H.tape x).z i:= (measurable_of_countable fun x:A.Slates=>code A x i).comp layoutP
lemma carn_m (i: Site (More N)): Measurable fun x=>(H.tape x).color i:= H.cones_m (panel A i)
lemma htHeight (i:A.Hcols): Measurable fun x=>(H.tape x).h i:=askM (fun x:η=> (H.tape x).z i) (H.cones_m i) (fun b x=> H.T.give H.y (Letters.window A (H.port x) i.1) i.2 b) (fun i'=> (H.T.give_meas _ _ _).comp ((cont_horizontal _).measurable.comp H.port_m))
lemma growM (i:A.Index)(z:Site (More N)): Measurable fun x=>(H.tape x).plant i z:=by have hp:= (Stamps.plant_m H.Z H.tile A i).comp (H.duoR_M i); change Measurable fun x:η=> Stamps.plant H.Z _ _ _ _ _ z; exact (measurable_pi_apply z).comp hp
lemma meatM (i:A.Index)(z:Site (More N))(v:ℝ): Measurable fun x=>(H.tape x).brush i v z:= by have hp:=(Stamps.brush_m H.Z H.tile A i v).comp (H.duoR_M i); exact (measurable_pi_apply z).comp hp
lemma heatM (i:Site (More N)): Measurable fun x=> (H.tape x).G i:= by unfold Letter.G; split; exact H.growM _ i; exact (measurable_of_countable fun j:Fin 5=> beacon j (zoneD (X:=A) i)).comp (H.carn_m i)
lemma tunesM (i:Site (More N))(v:ℝ): Measurable fun x=> (H.tape x).H X.W v i:=by
 have he(j) : Measurable fun p=> amend X.W (H.tape p) i j v := by
    let b:= (fun k:E× Op SU.Slot=> swivelC k.1 k.2); let d:=fun x=> closeC ((H.tape x).frameN i) ((H.tape x).color i); let G:=fun z=>neonT z ( Clipγ.gamma X.W.H (burial (A.mark j) i),v); have h₁: Measurable d:= (H.htHeight (panel A i)).inv.mul ((measurable_of_countable Mag.center).comp (H.carn_m i)); exact swivel_cont.measurable.comp (f:=fun x=> (d x,G ((H.tape x).color i))) (h₁.prodMk ((measurable_of_countable G).comp (H.carn_m i))) -- tune namespaces
 unfold Letter.H; split; split; exact he _; exact H.meatM _ i v; exact (measurable_of_countable fun k=> Kite.dict k (zoneD (X:=A) i,v)).comp (H.carn_m i)
lemma interestM : Measurable fun x=> Lily.interest A (H.tape x):=by
 refine measurable_pi_lambda _ fun i=>?_ ; unfold Lily.interest; split; exact H.meatM _ i 2; exact measurable_const
variable {Y:Driver N}{e d c:ℝ}{k:ℕ}{R X H}
lemma utiM (g: Measurable H.loom):Measurable H.utensil:= g.comp H.harbor_m
lemma threadM (g: Measurable H.loom):Measurable (H.thread R X):= askM (H.unsea R) (H.stares_m R) (fun M x=> way A R X (H.tape x) M (H.utensil x)) (fun i=> (tree_m ..).comp (f:=fun x=>(H.utensil x,(H.tape x).G)) ((utiM g).prodMk (measurable_pi_lambda _ fun i=> H.heatM i))) -- tune key explicit
lemma furyM (g:Measurable H.loom)(i:Site (More N))(v:ℝ): Measurable fun x=> H.fury R X x v i:=by
 let k:=fun (y: Seal (SiteX A R)) (x:η)=>tower A R X (H.tape x) y (H.utensil x) v i; apply askM (H.unsea R) (H.stares_m R) k; intro j; unfold k tower Kactual; split; next v=> exact SU.Pair.full_cont.measurable.comp (measurable_subtype_coe.comp ((measurable_pi_apply i).comp ((tree_m ..).comp (f:=fun x=>(H.utensil x,(H.tape x).G)) ((utiM g).prodMk (measurable_pi_lambda _ fun i=> H.heatM i))))) -- explicit
 next v=> exact H.tunesM _ i _ -- implicit order
abbrev ΓStage (F:Rented R H X Y.d e k c)(p:Stamp A R X Y) (x:H.castP):= α F p x.val x.property
variable (F:Rented R H X Y.d e k c) (p:Stamp A R X Y)
lemma Γ_m : Measurable (ΓStage F p):=by
 let t:=F.roof.bill; have he:= measurable_subtype_coe (p:=H.Role); let u:=H.fury R X; have ht(i:Site (More N))(v):Measurable (fun x:H.castP=> u x.val v i):= (furyM t i v).comp he; refine Measurable.subtype_mk (f:=fun i:H.castP=> (ΓStage F p i).val) ?_; refine portrait_meas _ _ ((utiM t).comp he) ((threadM t).comp he) (fun i=>?_ ) ht ?_ -- tune argument order & too deep
 · exact (H.stares_m R|>.comp he) (show MeasurableSet {x|i ∈ Picks A R x} from (Set.to_countable _).measurableSet) -- tune star.M
 intro i v; have hf (x:H.castP) : ContDiff ℝ ∞ (fun v=> u x.val v i):=(F.pay x.val x.property).licence.progress.Ksmooth i; exact deriv_φ _ (ht i) v (fun x=>(hf x).differentiable (by norm_num) v) -- namespace

end YM.CF.BPress.Sugar.Crew
