import YM.CF.DPress.FD.Stock.Pico
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Spire Skye Cash Deck MeasureTheory SU Lat Finset Wilson Laurent
open Cube (More Guard)
open scoped Topology BigOperators ENNReal NNReal Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{I:Type}[Fintype I]{r d:ℕ}{u t:ℝ}
namespace Spoke
variable (X:Scout I n u t r) (f:ℕ→ℝ→I)
local notation "D"=> Support (More n)
lemma bonnet_m (c:D) : Measurable (bonnet c) := by
 let p: Ids n→Seat n:= greet c ∘ priorP; exact mealM (F:=p) (fun i=> ((mastM c).comp primeV) (measurableSet_singleton _)) (G:=fun i x=> x i) (fun i=> measurable_pi_apply _)
section
variable [MeasurableSpace I][MeasurableSingletonClass I](h:∀ i,Measurable (f i))
include h
lemma well_m (S:D)(e:reach n): Measurable (fun P: Orbit n=>well X f S P.1 e P.2):=by
 unfold well; split; swap; exact measurable_pi_apply _ |>.comp measurable_fst
 let t(x:Orbit n):= bonnet S x.2; let i(x):=f S.card (t x).1; let Q(x:Orbit n):= (i x,(t x).2.1); have hp:Measurable t:=(bonnet_m _).comp (α:=Orbit n) measurable_snd; have ht: Measurable Q:=(h S.card|>.comp (measurable_fst.comp hp)).prodMk (measurable_fst.comp (measurable_snd.comp hp)); exact mealM (F:=Q) (fun j=> ht (measurableSet_singleton _)) (G:=fun x P=> mend (X.X x.1) x.2 P.1 e) (fun x=>(measurable_pi_apply _).comp ((mine (X.basicF _) _).meas.comp measurable_fst))
lemma glow_m (k:ℕ): Measurable (glow X f k):= measurable_pi_lambda _ fun e=> mealM (F:=fun x:Orbit n=> RG.flags u x.1) (fun V=> measurable_fst (RG.flags_measurable_eq ..)) (G:=fun V P=>well X f (soup V k e) P.1 e P.2) (fun V=>well_m X f h _ _)
lemma ray_m (k:ℕ): Measurable (ray X f k):=by
 have ht : Measurable (fun x:Orbit n => frameP x.2):= measurable_pi_lambda _ fun i=> measurable_snd.comp (measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd))
 have hv: Measurable fun x:(Seat n→E)×Pane n=> gauge x.1 x.2:=by apply Continuous.measurable; apply continuous_pi; intro i; simp only [Lattice.gauge]; fun_prop
 have hi: Measurable (fun (x:Orbit n) (i:Seat n)=> ((frameP x.2) i)⁻¹) := measurable_pi_lambda _ fun i=> ((measurable_pi_apply i).comp ht).inv
 let p:=fun x:Orbit n=> ((Lattice.gauge (frameP x.2) x.1),x.2); have hg : Measurable p:= (hv.comp (ht.prodMk measurable_fst)).prodMk measurable_snd; let z(x:Orbit n):=((frameP x.2)⁻¹,glow X f k (p x)); have hz:Measurable z := hi.prodMk ((glow_m X f h k).comp hg); rw [show ray X f k=(fun x:(Seat n→E)×Pane n=> Lattice.gauge x.1 x.2) ∘ z from rfl]; exact hv.comp hz
lemma ray_troof (p:r ≤ d)(a:ℝ)(uZ:∀ V:Pane n, RG.flags t V=∅→ Guard V a): Roof n u a d (ray X f d):=by
 refine ⟨fun x=> ?_,ray_m X f h _,fun V x g=> ray_g X f d _ _ _,fun V x g t=>ray_s X f d _ _ _ t, fun V x i t=> here X f d _ _ _ t, ray_t X f p⟩
 unfold ray; apply uZ; rw [RG.gauge_flags]; exact lit_g X f _ _ p
end
end Spoke
end YM.CF.DPress.FD
