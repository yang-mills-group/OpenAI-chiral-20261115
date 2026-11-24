import YM.CF.Broc.Surge
import YM.CF.Sample.Mist
set_option autoImplicit false
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Y J T D G: Type*}[Fintype Y][DecidableEq Y][TopologicalSpace D]
variable [Fintype J][DecidableEq J][TopologicalSpace T][MeasurableSpace T][CompactSpace T][BorelSpace T][SecondCountableTopology T][T2Space T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ]
abbrev Sam( A: D→Plan J μ) := ↥{p:D × (J→T)| fall (A p.1) p.2 ≠0}
def sampler(P:D→Plan J μ)(F: Sam P→ℂ) (x:D × (J→T)):= @dite _ (fall (P x.1) x.2 ≠0) (Classical.propDecidable _) (fun h=> F (⟨x,h⟩:Sam P)) fun _=>0
lemma sampler_p {A:D→Plan J μ}(F:Sam A→ℂ)(x: D×(J→T))(h:fall (A x.1) x.2≠0): sampler A F x= F (⟨x,h⟩:Sam A):=dif_pos h
def cream(P:D→Plan J μ)(F: Sam P→ℂ)(x:D× (J→T)):= fall (P x.1) x.2 • sampler P F x
def means(P:D→Plan J μ)(F: Sam P→ℂ)(x:D):ℂ:=∫ t:J→T, cream P F (x,t) ∂fares J μ
lemma cream_gift(P:D→ Plan J μ)(f: Sam P→ℂ)(k:ℝ)(v:Continuous (fun t:D × (J→T)=>fall (P t.1) t.2))(h:Continuous f)(p:∀ i,‖f i‖≤ k): Gift (fun t:D × (J→T)=>fall (P t.1) t.2) (sampler P f) k:=by
 refine soft (fun t=> sails_nonneg ..) ?_ v ?_
 · intro i hi; unfold sampler; rw [dif_pos hi]; exact p _
 intro x e; let S :Set (D × (J→T)) := {t| fall (P t.1) t.2≠0}; have he:IsOpen S:=isOpen_ne_fun v continuous_const; apply ContinuousWithinAt.continuousAt (s:=S) _ (he.mem_nhds e)
 have hf:ContinuousOn (sampler P f) S:=by
   rw [continuousOn_iff_continuous_restrict]; exact h.congr (fun x=> (sampler_p f x.val x.property).symm) -- tune
 exact hf x e
lemma means_val(P:D→Plan J μ)(F:Sam P→ℂ)(u:ℝ)(v:Continuous (fun p:D × (J→T)=>fall (P p.1) p.2))(h: Continuous F)(p:∀ x,‖F x‖ ≤u)(x:D): ‖means P F x‖≤u:=by
 let V:= P x; let T(J:J→T):=(x,J); let q:=cream_gift P F u v h p; have hf: Continuous T:= continuous_const.prodMk continuous_id
 let k:= q.pullGift T hf; exact cap_mean (μ:=fares _ μ) _ _ k.bounded k.pos (v.comp hf) k.weighted (sails_all V)
variable {b : Light Y D G}
structure Lit (A: D→Plan J μ) (b : Light Y D G) (S: Seal Y→ Finset J) where
 pollen : G → ((J→ T) ≃ᵐ (J→ T))
 level (g):MeasurePreserving (pollen g) (fares J μ) (fares J μ)
 gauge x t g : fall (A (b.dress g x)) (pollen g t)= fall (A x) t
 phase : Continuous (fun x:D×(J→T) => fall (A x.1) x.2)
 spread : Monotone S

namespace Lit
variable {A:D→Plan J μ}{S:Seal Y→Finset J}(L:Lit A b S)
def pool(g:G)(x:Sam A):Sam A :=⟨(b.dress g x.val.1,L.pollen g x.val.2),by change _≠0; rw [L.gauge]; exact x.property⟩
def botL :Light Y (Sam A) G where
 frame := b.frame
 dress := L.pool
 rel T x y:= b.rel T x.val.1 y.val.1 ∧ AgreeF (S T) x.val.2 y.val.2
 expands s t h x y p:= ⟨b.expands s t h _ _ p.1,p.2.less (L.spread h)⟩
lemma inoc (f:Sam A→ℂ){T: Seal Y} (h:∀ v w,L.botL.rel T v w→ f v=f w)(k:ℝ)(hp:Continuous f)(hq:∀ i,‖f i‖ ≤ k)(x y:D)(hx:b.rel T x y)(H:Finset J)(he:S T⊆ H)(hh:Bank (A x) H)(hd:Bank (A y) H)(hl:∀ z, sails (A x) H z=sails (A y) H z):means A f x=means A f y:=by
 let v:= fun t=> sampler A f (x,t); let w:=fun t=>sampler A f (y,t); let p:=cream_gift A f k L.phase hp hq
 apply banks_like (A x) (A y) v w hh hd hl _ ((p.pullGift (fun t=>(x,t)) (continuous_const.prodMk continuous_id)).weighted) ((p.pullGift (fun t=>(y,t)) (continuous_const.prodMk continuous_id)).weighted)
 intro X Y hB u k; unfold v w sampler; rw [dif_pos u,dif_pos k]; exact h _ _ ⟨hx,hB.less he⟩
lemma tide (F:Sam A→ℂ){K:ℝ}{S0 : Seal Y}(p:Peak L.botL S0 F K)(x:D)(g:G): means A F (b.dress g x)=means A F x:=by
 let P:=L.level g; unfold means; rw [←P.integral_comp (L.pollen g).measurableEmbedding]; apply integral_congr_ae; apply Eventually.of_forall; intro i
 change fall (A _) _ • sampler _ _ _=fall (A x) i • sampler _ _ _; rw [L.gauge]; by_cases h:fall (A x) i≠0
 · let v: Sam A:=⟨(x,i),h⟩; let w:=L.pool g v
   rw [sampler_p F (b.dress g x,L.pollen g i) w.property,sampler_p F (x,i) v.property]; exact congrArg (fun j:ℂ=> fall (A x) i • j) (p.gauge v g)
 rw [not_not] at h; rw [h,zero_smul,zero_smul]
section tap
variable [LocallyCompactSpace D][FirstCountableTopology D]
lemma box {K:ℝ} {F:Sam A→ℂ}{Q: Seal Y}(R:Peak L.botL Q F K): Continuous (means A F):=(cream_gift A F K L.phase R.cont R.sumline).settled
lemma loot {F: Sam A→ℂ}{a K:ℝ} (R: Seat L.botL F a K)(t:Seal Y→Finset J)(h:∀ x T,Bank (A x) (t T))(he:∀ T,S T ⊆ t T)(p: ∀ T x y,b.rel T x y→∀ z,sails (A x) (t T) z=sails (A y) (t T) z): Seat b (means A F) a K:=by
 obtain ⟨V,C,H,Y⟩:=R
 let M (i):=means A (V i)
 refine ⟨M,C,⟨fun i=> ?_,H.pays⟩,?_⟩
 · let T:=H.ordered i
   exact ⟨T.pos,T.travel,L.box T,means_val A _ _ L.phase T.cont T.sumline,fun p' q e=>L.inoc (V i) T.reads (C i) T.cont T.sumline p' q e (t i) (he i) (h p' i) (h q i) (p _ p' q e), L.tide _ T⟩ -- tune hologram
 intro x
 unfold M means; rw [←integral_finsetSum]
 · apply integral_congr_ae; apply Eventually.of_forall; intro y; by_cases h: fall (A x) y=0; · simp only [cream, h, zero_smul,sum_const_zero] -- remove
   unfold cream; simp_rw [sampler_p _ (x,y) (show fall (A (x,y).1) (x,y).2≠0 from h)]; rw [Y]; exact Finset.smul_sum ..
 intro i _; exact net_compact ((cream_gift A (V i) (C i) L.phase (H.ordered _).cont (H.ordered _).sumline).weighted.comp (show Continuous (fun y:J→_ =>(x,y)) from continuous_const.prodMk continuous_id))
end tap
end Lit
end YM.CF.Broc
