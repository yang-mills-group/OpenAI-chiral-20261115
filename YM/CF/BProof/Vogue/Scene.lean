import YM.CF.BProof.Vogue.Into
/-! Changing depot expectation to a single stencil bank. All reads use
nominal U, no null events. This covers inquiries additional to P law on
frame array (not arbitrary other tags). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh Shore Finset Equiv
open scoped Topology BigOperators NNReal ENNReal Classical
variable {K: Type} [Fintype K][Nonempty K][MeasurableSpace K][MeasurableSingletonClass K]{n:Side}{d u:ℝ}{k r L:ℕ}(P:Spice n K d u k L)
def joint(U: Pane n)(x:K × Root n): Root n × Pane n:=(x.2,gauge x.2⁻¹ (P.P x.1 (gauge x.2 U)))
lemma joint_m(U: Pane n):Measurable (joint P U):=by
 unfold joint; apply measurable_snd.prodMk; refine gaugeP.comp (f:=fun x:K × Root n=> (x.2⁻¹, P.P x.1 (gauge x.2 U))) (measurable_snd.inv.prodMk ?_); exact Skye.mealM (F:=Prod.fst) (fun i=>measurable_fst (measurableSet_singleton i)) (fun i=> (P.ok i).meas.comp (gaugeP.comp (measurable_snd.prodMk measurable_const))) -- f param infer
-- utility covariance map
lemma mapPull {X Y Z:Type*}[MeasurableSpace X][MeasurableSpace Y][MeasurableSpace Z]{f:X→Y}{g:Y→ Z}{μ:Measure X}{ν:Measure Y}(h:MeasurePreserving f μ ν)(p:Measurable g) : μ.map (g ∘ f)=ν.map g:=by rw [← Measure.map_map p h.measurable,h.map_eq]
lemma ident (p:k≤ r)(h:k+1+(k+1)+L≤2*r+20)(U:Pane n):
    (depot n).map (fun t=>(frameP t, conic P r (U,t)))=((paperMeas K).prod (rootM n)).map (joint P U):=by
 let M:=RG.flags u U; let X(g:Root n):= gauge g U; have ht(g): M=RG.flags u (X g):=(RG.gauge_flags ..).symm; let B(v:BoardB M r K × Root n): Root n×Pane n:= (v.2,gauge v.2⁻¹ (seed_at P M (X v.2) v.1))
 have he:Measurable B:=by
    unfold B; apply measurable_snd.prodMk; apply gaugeP.comp (f:=fun x:BoardB M r K × Root n=> (x.2⁻¹,seed_at P M (X x.2) x.1)) (measurable_snd.inv.prodMk _); exact mealM (F:=Prod.fst) (fun i=>measurable_fst (measurableSet_singleton i)) (fun i=>(seed_meas P M i).comp (gaugeP.comp (measurable_snd.prodMk measurable_const)))
 let f(t:Ids n): BoardB M r K × Root n:= (skill M K t,frameP t); have hT:= rawmp (r:=r) (K:=K) M
 rw [show (fun t:Ids n=>(frameP t,conic P r (U,t)))=B ∘ f from ?_, mapPull hT he]; swap; · funext t; dsimp only [B,f, X, Function.comp_apply, conic]; rw [skills P t _ (ht (frameP t))]
 let T:=BoardB M r K; let μ:= (paperMeas (K× T)).prod (rootM n); let y(a:(K × T) × Root n):=(a.1.2,a.2); let z (a:(K × T) × Root n):=(a.1.1,a.2)
 have hm : MeasurePreserving y μ ((paperMeas T).prod (rootM n)):= by unfold μ; rw [parcelPair]; exact measurePreserving_snd.prod (MeasurePreserving.id _)
 have hu : MeasurePreserving z μ ((paperMeas K).prod (rootM n)):= by unfold μ; rw [parcelPair]; exact measurePreserving_fst.prod (MeasurePreserving.id _)
 obtain ⟨E,J,u'⟩:= shuffle P M p h; let V(e: Perm (K × T)):=Prod.map (⇑e) (id (α:=Root n)); have hE(e: Perm (K×T)):MeasurePreserving (V e) μ μ:= (orderMP e).prod (MeasurePreserving.id _)
 rw [←mapPull (hm.comp (hE E)) he, ←mapPull (hu.comp (hE J)) (joint_m P U)]
 apply congrArg (fun f => μ.map (f : _→Root n × Pane n)); funext i; exact Prod.ext rfl (congrArg (fun x=> gauge i.2⁻¹ x) (u' _ (ht i.2) i.1))
end YM.CF.BProof.Vogue
