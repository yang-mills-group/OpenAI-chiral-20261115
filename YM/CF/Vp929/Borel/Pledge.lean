import YM.CF.Vp929.Borel.Scoop
set_option autoImplicit false
set_option maxHeartbeats 680000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory
open Mesh Lattice Atlas Skye Cane Spire Scroll SU Cube Lat Aerial Sample Gather
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
namespace Scoop
variable (n:Side)(r:ℕ)
variable {I:Type} [Nonempty I][Fintype I][MeasurableSpace I][MeasurableSingletonClass I][StandardBorelSpace I]
variable (p:Ticket I)(R:Sweep n→Equiv.Perm I)
variable (v:∀s,MeasurePreserving (R s) p.Law p.Law)
variable {A:Type} [Fintype A][MeasurableSpace A][MeasurableSingletonClass A]
variable (f k:ℕ) (T:Budget r f k) (F:I→Seat n→A)
variable (h:∀ S V,stone (More n) S V k→ Ticket.Indep p (Vision S F) (Vision V F))
variable (u d:ℝ)(Q:I→Pane n→Pane n)
variable (a:∀i,Basic n (Q i) u d f)
variable (t:∀ s i,mend (Q i) s=Q (R s i))
variable (g:∀i j,∀ e:reach n,(∀ x∈ Read.glow _ e f,F i x= F j x)→∀ V:Pane n,Q i V e= Q j V e)
lemma gauging{A:Type*}[MeasurableSpace A]{f:A→ Frame n}{g:A→Pane n} (F:Measurable f)(G:Measurable g): Measurable fun x=>gauge (f x) (g x):=by
 let k : (Frame n)× Pane n→Pane n:= fun q=> gauge q.1 q.2; change Measurable (k ∘ (fun x=>(f x,g x))); exact (Braid.gaugesM n).comp (show Measurable (fun x=>(f x,g x)) from F.prodMk G)
lemma inverseG{A:Type*}[MeasurableSpace A]{f:A→Frame n}(F:Measurable f):Measurable fun a=> (f a)⁻¹:= measurable_pi_lambda _ fun i=> ((measurable_pi_apply i).comp F).inv
include a in
lemma pinnacleM(V:Pane n)(i:I) : Measurable fun x:Frame n => gauge x⁻¹ (Q i (gauge x V)):=by
    apply gauging n (f:=fun x:Frame n=> x⁻¹); · exact inverseG n (f:=id) measurable_id
    exact (a i).meas.comp (gauging n (f:=fun x:Frame n=>x) measurable_id (g:=fun _=> V) measurable_const)
include a T t v h g
theorem pledge (V:Pane n) : (depot n).map (fun z=> Braid.spring n r u Q (samp n p) (V,z))= ((valsf n).prod p.Law).map (fun x=> gauge x.1⁻¹ (Q x.2 (gauge x.1 V))) :=by
 have z:f ≤ r:= by unfold Budget at T; omega
 let P:= Braid.spring n r u Q (samp n p); let F(ω:Frame n × Wave n):= P (V,merge n ω); let x(ω:Frame n×I):=gauge ω.1⁻¹ (Q ω.2 (gauge ω.1 V)); have H:=Braid.springM n r u d Q (samp n p) (fun i=> Paper.bigger (a i) z) (fun S=>(stint n p S).1); have hb:Measurable x:=by
    apply mealM (F:=fun ω: Frame n × I=> ω.2) (G:=fun i ω=> gauge ω.1⁻¹ (Q i (gauge ω.1 V))) (fun _=> measurable_snd (measurableSet_singleton _)); intro i; exact (pinnacleM n f u d Q a V i).comp measurable_fst
 have ht(G:Frame n): (valsw n).map (fun i=> F (G,i))= p.Law.map (fun i=>x (G,i)):=by
    let A:=gauge G V; have ht(w:Wave n):frameP (merge n (G,w))=G:= rfl; let f':= fun U:Pane n=> gauge G⁻¹ U; have M:Measurable f':=gauging n measurable_const measurable_id; let u':= fun w:Wave n=> Braid.story n r u Q (samp n p) A (merge n (G,w)); let v':=fun i:I=> Q i A; let VV(w:Wave n):Orbit n:=(A,merge n (G,w)); have tV:Measurable VV:= measurable_const.prodMk ((mergeM n).1.comp (measurable_const.prodMk measurable_id)); have ht:Measurable u':= by
       unfold u'; change Measurable ((fun x:Orbit n=>Braid.story n r u Q (samp n p) x.1 x.2)∘ VV); exact (Braid.meterP n r u d Q (samp n p) (fun i=>Paper.bigger (a i) z) fun V=>(stint n p V).1).comp tV
    have hv := join_law n r p R v f k T (F:=_) h u d Q a t g A G; change Measure.map u' (valsw n)=p.Law.map v' at hv; change Measure.map (f'∘u') _ = Measure.map (f'∘v') _; rw [← Measure.map_map M ht, hv,Measure.map_map M (measurable_of_countable _)]
 let y(z:Ids n):= P (V,z); have he:Measurable y:= H.comp (measurable_const.prodMk measurable_id); change Measure.map y _=((valsf n).prod p.Law).map x; rw [← (mergeM n).map_eq,Measure.map_map he (mergeM n).1]; exact mixedMap _ _ _ (show Measurable F from he.comp (mergeM n).1) hb ht
end Scoop
end YM.CF.VolumeCape.Borel
