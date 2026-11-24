import YM.CF.Vp929.Borel.Pledge
set_option autoImplicit false
set_option maxHeartbeats 660000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Mesh Lattice Rooms Atlas Guide MeasureTheory Palace Mos Mesa Cube Lat Skye Read Cane Spire Scroll Laurent Paper SU ProbabilityTheory Borel
open scoped Topology Classical NNReal ENNReal Matrix.Norms.Frobenius
variable (C:Side)(K:ℕ→ℝ)(n:Side)(p:2*(spanR*Bolt C)<(More n).val)
namespace Dream
open Borel.Aerial Borel.Sample Borel.Scoop
instance : MeasurableSpace Arm:=⊤
instance :MeasurableSingletonClass Arm:=⟨fun _=>trivial⟩
def reachT(C:Side):ℕ:=3*(spanR*Bolt C)
local notation "A_"=> More n
local notation "d_"=> demand (More n) p
local notation "i_"=> Sent (More n) p
local notation "f_"=>Aerial.Frame n
local notation "m_"=>Read.Wor (More n) C
local notation "R_"=> Fringe C
-- single rule
abbrev sceneQ (V: Pane n)(z:f_ × m_): Pane n:= gauge z.1⁻¹ (edition C K A_ z.2 (gauge z.1 V))
lemma sceneM: Measurable fun z: Pane n × (f_×m_)=> sceneQ C K n z.1 z.2:=by
 let g(x:Pane n × (f_×m_)):= x.2.1; have h: Measurable g:= measurable_fst.comp measurable_snd; have t:= gauging n h (measurable_fst (β:=f_ × m_) (α:=Pane n)); unfold sceneQ; apply gauging n (f:=fun z=>(g z)⁻¹) (inverseG n h); refine mealM (F:=fun x: Pane n×(f_×m_)=> x.2.2) (fun _=> (measurable_snd.comp measurable_snd) (measurableSet_singleton _)) (G:=fun W x=>edition C K A_ W (gauge x.2.1 x.1)) (fun W=>(editionC C K _ W).comp t)
lemma sceneL (V W: Pane n) (a b:f_ × m_)(e:reach n)(p:Agrees (↑(win R_ e)) V W)(t:Set.EqOn a.1 b.1 ↑(win R_ e))(r:Set.EqOn a.2 b.2 ↑(win R_ e)): sceneQ C K n V a e=sceneQ C K n W b e :=by
 let F:= win R_ e; have h:= tied F V W a.1 b.1 p t; let v:= halo_subset R_ (Skye.ends e); have ht:Read.glow _ e R_⊆F:=fun i k=> by obtain ⟨u,e,k⟩:= halo_spec.mp k; exact halo_spec.mpr ⟨u,(mem_singleton.mp e).symm ▸ mem_insert_self ..,k⟩
 have y:= editionL _ K A_ _ _ a.2 b.2 e (agrees_mono h ht) (r.mono (show _ from fun i v=>ht v)); unfold sceneQ; change ((a.1 e.1)⁻¹)*edition C K _ _ (gauge a.1 V) e*((a.1 (e.1+step e.2))⁻¹)⁻¹=_; rw [y,t (show e.1∈ (↑F:Set (Seat n)) from v (by simp)),t (show e.1+step e.2∈ (↑F:Set (Seat n)) from v (by simp))]; rfl
-- finite mark dependence. Aerial.valsf = iid Haar. Map equality for every fixed configuration.
def Haven (P: Orbit n→Pane n):Prop:= ∃ μ : Measure (Wor A_ C), IsProbabilityMeasure μ ∧ (∀ S T,stone A_ S T (reachT C)→IndepFun (Vision S id) (Vision T id) μ) ∧ ∀ V:Pane n, (depot n).map (fun z=> P (V,z)) = ((Aerial.valsf n).prod μ).map (sceneQ C K n V)
private lemma pullMark{U I V:Type}[MeasurableSpace I][MeasurableSpace U][MeasurableSpace V][MeasurableSingletonClass I][MeasurableSingletonClass U][Countable I][Countable U](μ:Measure I)(f:I→ U){B:Type}[MeasurableSpace B](x:U→V)(y:U→B)(h: IndepFun (x∘f) (y∘f) μ) : IndepFun x y (μ.map f):=by
 apply indepFun_iff_measure_inter_preimage_eq_mul.mpr; intro s t hs ht; rw [Measure.map_apply (measurable_of_countable _) (((measurable_of_countable _) hs).inter ((measurable_of_countable _) ht)),Measure.map_apply (measurable_of_countable _) ((measurable_of_countable _) hs),Measure.map_apply (measurable_of_countable _) ((measurable_of_countable _) ht), Set.preimage_inter]; exact h.measure_inter_preimage_eq_mul _ _ hs ht
variable (r:ℕ) {u v:ℝ}(T:Sweater C (Delta.roofLength granite) K u v) (H:Borel.Gather.Budget r (Fringe C) (reachT C))
def spindle (u:ℝ) := Braid.spring n r u (Paper.Assembly C K n p) (Sample.samp n d_)
include T H
lemma covering (d:ℝ)(v':∀A:Pane n,RG.flags v A=∅→ Guard A d): Roof n u d r (spindle C K n p r u):= by
 apply Braid.springH n r u v (Paper.Assembly C K n p) _ _ (tokens n d_) (fun i=> (stint n d_ i).1) _ v'; intro i; exact bigger (Paper.Vow C K n p i T) (by unfold Gather.Budget at H; omega)
omit T H
private abbrev xMark := patchM A_ p
private abbrev χM := (demand A_ p).Law
private def PermY(t:Sweep n):= (revert A_ p (edit n t)).symm
private lemma disjQ(a b)(t:stone A_ a b (reachT C)): (demand A_ p).Indep (Vision a (xMark C n p)) (Vision b (xMark C n p)) := by
 obtain ⟨d,H,v⟩:=Mesh.scent A_ p; apply v; rw [H]; exact t
private lemma permA(t:Sweep n): MeasurePreserving (PermY C n p t) (demand A_ p).Law (demand A_ p).Law:= Ticket.cost d_ _ fun i=>by have e:=reverts A_ p (PermY C n p t i) (edit n t); unfold PermY at *; rw [Equiv.apply_symm_apply] at e; exact e.symm
private lemma permTruth(t:Sweep n)(i:i_): mend (Paper.Assembly C K n p i) t=Paper.Assembly C K n p (PermY C n p t i):= by have he:= Paper.allayed C K n p (PermY C n p t i) t; unfold PermY at *; rw [Equiv.apply_symm_apply] at he; exact he
private lemma qL(i j:Sent (More n) p)(v:reach n)(k:∀ x'∈Read.glow _ v R_, xMark C n p i x'=xMark C n p j x') (V:Pane n): Paper.Assembly C K n p i V v=Paper.Assembly C K n p j V v:= editionL C K _ V V (patchM A_ p i) (patchM A_ p j) _ (fun _ _ _=>rfl) (fun x v=> k x v)
private lemma rollMark(V:Pane n) : ((Aerial.valsf n).prod (Measure.map (xMark C n p) (χM C n p))).map (sceneQ C K n V) = ((Aerial.valsf n).prod (χM C n p)).map (fun y=> sceneQ C K n V (y.1,xMark C n p y.2)):=by
 let M:=Measure.map (xMark C n p) (χM C n p); let g:= Prod.map (id:f_→ _) (xMark C n p); have w: MeasurePreserving g ((Aerial.valsf n).prod (χM C n p)) ((Aerial.valsf n).prod M):=(MeasurePreserving.id _).prod (show MeasurePreserving (xMark C n p) (χM C n p) M from ⟨measurable_of_countable _,rfl⟩); have he:Measurable (sceneQ C K n V):=(sceneM C K n).of_uncurry_left
 change Measure.map (sceneQ C K n V) ((Aerial.valsf n).prod M)=_; rw [← w.2,Measure.map_map he w.1]; rfl
private lemma joinI(a b)(h:stone (More n) a b (reachT C)): IndepFun (Vision a (id:m_→_)) (Vision b (id:m_→_)) (Measure.map (xMark C n p) (χM C n p)) := pullMark (χM C n p) (xMark C n p) _ _ (Ticket.cashInd d_ (disjQ C n p _ _ h))
include T H
private lemma pressure(V:Pane n):(depot n).map (fun z : Ids n=> spindle C K n p r u (V,z))=((Aerial.valsf n).prod (χM C n p)).map (fun y=> sceneQ C K n V (y.1,xMark C n p y.2)):=Borel.Scoop.pledge n r d_ (PermY C n p) (permA C n p) R_ (reachT C) H (xMark C n p) (disjQ C n p) u v (Paper.Assembly C K n p) (fun i=> Paper.Vow _ _ _ _ i T) (permTruth C K n p) (qL C K n p) V
lemma heaven : Haven C K n (spindle C K n p r u):= by
 refine ⟨Measure.map (xMark C n p) (χM C n p),Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable,joinI C n p,fun V=>?_⟩
 exact (pressure C K n p r T H V).trans (rollMark C K n p V).symm
end Dream
end YM.CF.VolumeCape
