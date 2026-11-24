import YM.CF.DPress.FD.Stock.Frame
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory SU Lat Finset Wilson Laurent OrderF BasicIid Spoke Gear
open Cube (More Guard)
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{J:Type}[Fintype J][MeasurableSpace J][MeasurableSingletonClass J]{r d:ℕ}{u t:ℝ}
namespace Star
variable (X:Scout J n u t r)(f:ℕ→ℝ→J) (A:Pane n)
abbrev Coral(n:Side):= Measure.pi (fun _:Seat n=> group.probHaar)
-- tag-formation product (Coral,Pack)
lemma shuffle : MeasurePreserving (uncurry (@Masters n)) ((Coral n).prod (Pack n)) (depot n):=by
 let G:= Seat n → E; let P:=Coral n; let Y:=Seed.heightLaw n; let T:=yawP n; let A:=Y.prod T;
 -- (G,(H,Y)) -(swap)-> ((H,Y),G) -assoc-> H,(Y,G). then combine Y,G.
 let L:=Sweep n × E; let I:= (Seed.ℐ:Type); let V(i:Seat n) := paperMeas (Sweep n); let H:= Measure.pi (fun i:Seat n=> (V i).prod group.probHaar);
 have ht:MeasurePreserving (fun x : Yaw n× G => fun i=> (x.1 i,x.2 i)) (T.prod P) H:= MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow _ _ _) (measurePreserving_arrowProdEquivProdArrow _ _ _ V (fun _=>group.probHaar)) -- tune
 let Hp := Measure.pi (fun _:Seat n=>pale); have hg:MeasurePreserving (fun x:Seed.Stage n=> Seed.pri x) Y Hp :=measurePreserving_pi (f:=fun _=> Subtype.val) (fun _=> volume) (fun _=>pale) (fun i=> unitInterval.measurePreserving_coe) -- tune inference I
 have hz: MeasurePreserving (fun x: (Seat n→ℝ) × (Seat n→ L) => fun i=> (x.1 i,x.2 i)) (Hp.prod H) (depot n):= MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ..) (measurePreserving_arrowProdEquivProdArrow ℝ L (Seat n) (fun _=> pale) (fun i=> (paperMeas (Sweep n)).prod group.probHaar)) -- tune á
 exact hz.comp ((hg.prod ht).comp ((measurePreserving_prodAssoc Y T P).comp Measure.measurePreserving_swap)) -- constant Pack.T.Field.
-- full joint-realization $output.P$. per field.V not requiring Sound
abbrev fairly (T:Scout J n u t r)(A:Pane n)(g:Seat n→ E)(i:J): Pane n:= gauge g⁻¹ (T.X i (gauge g A))
private lemma gauges_M : Measurable fun x:(Seat n→E) × Pane n=> gauge x.1 x.2:=by apply Continuous.measurable; apply continuous_pi; intro i; simp only [Lattice.gauge]; fun_prop
private lemma funU {B C Y:Type*}[MeasurableSpace B][MeasurableSpace C][MeasurableSpace Y] (p:B→Y→C)(hp:Measurable (uncurry p))(φ:B→Y)(h:Measurable φ) : Measurable fun i=> p i (φ i):= hp.comp (measurable_id.prodMk h)
private lemma measQ (F:J→Pane n→Pane n) (v:∀ i,Measurable (F i)) : Measurable (uncurry F):=by
 exact mealM (F:=Prod.fst) (fun i=> (measurable_fst (β:=Pane n)) (measurableSet_singleton i)) (G:=fun i x=> F i x.2) (fun i=> (v i).comp measurable_snd)
private lemma action_m {U: Type*}[MeasurableSpace U] (f:U→(Seat n→E))(g:U→Pane n)(h:Measurable f)(v:Measurable g): Measurable (fun x=>Lattice.gauge (f x) (g x)):=by
   unfold Lattice.gauge; apply measurable_pi_lambda; intro i; fun_prop
lemma fair_m : Measurable fun (x: (Seat n→E) × J)=> fairly X A x.1 x.2:= by
 let f (x:(Seat n→E) × J):= X.X x.2 (Lattice.gauge x.1 A); have ht: Measurable f:= (measQ X.X (fun i=> (X.basicF i).meas)).comp (measurable_snd.prodMk (action_m _ (fun _=>A) measurable_fst measurable_const)); let g(x:(Seat n→E)× J)(i:Seat n):=(x.1 i)⁻¹; have hg:Measurable g:= measurable_pi_lambda _ (fun i=> ((measurable_pi_apply i).comp measurable_fst).inv); exact action_m _ f hg ht
variable (Z:∀ i, Measurable (f i)) (h:∀ S:Wheel n,S.Nonempty→ MeasurePreserving (fun x=> f S.card (Seed.pick S x).val) (Seed.heightLaw n) X.V.c.PM) (p:100*r ≤ d)
include p Z h
private lemma hv(nu:Pane n)(g: Seat n→E):(Pack n).map (fun x:Duo n=> glow X f d (nu,Masters g x))= X.V.c.PM.map (fun i=>X.X i nu):=by
    let S:=RG.flags u nu; let T:=amber X f S h d; rw [show (fun x:Duo n=> glow X f d (nu,Masters g x))= made X nu d ∘ figs X f S d from (funext fun i=> fig_U X nu f d i g), ←Measure.map_map (measurable_of_countable (made X nu d)) T.measurable,T.map_eq]; exact moon_p X nu p
private lemma cue(g:Seat n→ E): (Pack n).map (fun x:Duo n=> ray X f d (A,Masters g x)) = X.V.c.PM.map (fairly X A g):=by
 let G:= gauge g A; have hk (x:Duo n):frameP (Masters g x) = g:= rfl; have he:(fun x=> ray X f d (A,Masters g x))=Lattice.gauge g⁻¹ ∘ (fun x:Duo n=> glow X f d (G,Masters g x)):=rfl; let Ψ : Measurable (gauge g⁻¹ (R:=Per (More n)) (K:=group.El)) := by change Measurable (fun x:Pane n=> Lattice.gauge g⁻¹ x); apply action_m (fun _=>g⁻¹) id measurable_const measurable_id -- tune binder
 have hl: Measurable (fun x:Duo n=> glow X f d (G,Masters g x)):=(glow_m X f Z d).comp ((measurable_const).prodMk ((@shuffle n).measurable.comp measurable_prodMk_left))
 rw [he, ←Measure.map_map Ψ hl,hv X f Z h p G g,Measure.map_map Ψ (measurable_of_countable _)] -- tune
 rfl
lemma reality : (depot n).map (fun y=> ray X f d (A,y)) = ((Coral n).prod X.V.c.PM).map (uncurry (fairly X A)):=by
 let F:=fun (g:Seat n→ E) (x:Duo n)=> ray X f d (A,Masters g x); let Q:= fairly X A; let V:= fun y=> ray X f d (A,y); have ht:Measurable V := (ray_m X f Z d).comp measurable_prodMk_left
 rw [← (@shuffle n).map_eq,Measure.map_map ht (@shuffle n).measurable]; refine BasicIid.leaf F Q (ht.comp (@shuffle n).measurable) (fair_m X A) (fun g=> cue X f A Z h p g)
end Star
end YM.CF.DPress.FD
