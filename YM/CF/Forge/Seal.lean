import YM.CF.Forge.Arc
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open Jet
variable {A F E H α:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup H][NormedSpace ℝ H][TopologicalSpace α]
variable {f:A→α→ Config G c→F}{W:Set (Config G c)}{I:Finset (Bond c)}{n:ℕ}{C:ℝ}
namespace Arbor
section int
variable [MeasurableSpace A][FirstCountableTopology α][CompleteSpace F]
variable (p:IsOpen W)(h:∀ i, Arbor W (f i) I n C)(hp:0 ≤ C)(g:∀ x∈ W,∀ t:α, StronglyMeasurable (fun i=> f i t x)) (μ:Measure A)[IsFiniteMeasure μ]
include h g μ p hp
lemma ripple : Arbor W (fun t x=>∫ i,f i t x ∂μ) I n (μ.real Set.univ*C) ∧ ∀ (u:Config G c) (t:α)(x: Directions G c),gyrate I u x∈W → ∀ j, j≤n → Integrable (fun i=>iteratedFDeriv ℝ j (f i t ∘ gyrate I u) x) μ ∧ iteratedFDeriv ℝ j (fun x' =>∫ i, f i t (gyrate I u x')∂μ) x=∫ i, iteratedFDeriv ℝ j (f i t ∘ gyrate I u) x ∂μ:=by
 let X(u:Config G c):= gyrate I u ⁻¹' W; have hu(u:Config G c) : IsOpen (X u):= p.preimage (stickU _ u)
 have he(u:Config G c)(t:α)(x:Directions G c)(v:x∈X u): let P(i)(t)(x):= f i t (gyrate I u x);
                                                                          Warm (fun t x' =>∫ i,P i t x' ∂μ) n (t,x) ∧ ∀ j, j≤n→ Integrable (fun i=>iteratedFDeriv ℝ j (P i t) x) μ ∧ iteratedFDeriv ℝ j (fun y=> ∫ i, P i t y ∂μ) x=∫ i,iteratedFDeriv ℝ j (P i t) x ∂μ:=by
    intro P; let Y:= X u∩Metric.ball 0 (‖x‖+1); have hs:IsOpen Y:=(hu u).inter isOpen_ball; have hg:x∈Y:=⟨v, mem_ball_zero_iff.mpr (lt_add_one ..)⟩; have hx :∀ᶠ i in 𝓝 x,i∈Y := hs.mem_nhds hg
    obtain ⟨D,hd,B⟩:= lime (E:=F) (α:=α) G I n (‖x‖+1) C hp
    have hw(t)(i)(y)(m:y∈Y): Allows n (P i t) y D:=B (f i) (h i) t u y m.1 m.2
    have hh(t):Under μ (fun i=> P i t) n Y (fun _=>D):=under hs (fun i y v=> (hw t i y v).smooth) (fun i p=>g _ p.1 t) (integrable_const D) (hw t)
    refine ⟨⟨?_,fun i hi=>?_⟩,fun i hi=>⟨(hh t).integrate hg hi, ((hh t).less hi).differentiate hs hg⟩⟩
    · exact (continuousAt_snd (p:=(t,x)) |>.tendsto.eventually hx).mono fun y v=> (hh y.1).germ hs v
    have ht(i':α× Directions G c)(p:i'.2 ∈ Y): iteratedFDeriv ℝ i (fun y=>∫ i, P i i'.1 y ∂μ) i'.2=∫ z,iteratedFDeriv ℝ i (P z i'.1) i'.2∂μ:= ((hh i'.1).less hi).differentiate hs p
    let L: A→α × Directions G c→(Directions G c [×i]→L[ℝ] F):=fun i' y=> iteratedFDeriv ℝ i (P i' y.1) y.2; have hX : ∀ᶠ y:α× Directions G c in 𝓝 (t,x),y.2∈Y:=continuousAt_snd.tendsto.eventually hx
    have he :ContinuousAt (fun v=> ∫ z, L z v ∂μ) (t,x) := continuousAt_of_dominated (F:=fun i z=> L z i) (hX.mono fun y hy=> ((hh y.1).integrate hy hi).aestronglyMeasurable) (hX.mono fun y hy=> Eventually.of_forall fun z=>(hw _ z _ hy).norm_le i hi) (integrable_const D) (Eventually.of_forall fun i'=> ((h i').laurel u x v t).light i hi) -- tune
    apply he.congr_of_eventuallyEq (hX.mono ht)
 refine ⟨fun u v t=> ?_,fun u t x hp=> (he u t x hp).2⟩
 obtain ⟨hp',H⟩:=he u t 0 (show gyrate I u 0∈W from (born I u).symm ▸ v); refine ⟨hp',hp'.today,fun i hi=> ?_⟩
 let R(i'):=(fun x=>f i' t (gyrate I u x)); change ‖iteratedFDeriv ℝ i (fun x=>∫ z,R z x ∂μ) 0‖≤_; rw [(H i hi).2]
 calc
   _ ≤ _ := norm_integral_le_integral_norm _
   _ ≤ ∫ i,C∂μ := integral_mono ((H i hi).1.norm) (integrable_const _) (fun z=> (h z u v t).2.norm_le i hi)
   _ = _:= by simp
end int
section charge
variable {N:Type} [NormedAddCommGroup N] [NormedSpace ℝ N]{F:E→ H}{K: α→ Config G c→ N}
variable {C D:ℝ}
lemma cost_up(h: Arbor W K I n C)(v:C ≤ D): Arbor W K I n D:=fun u p t=>⟨(h u p t).1,(h u p t).2.mono v⟩
lemma shrunk (h: Arbor W K I n C){Y:Set (Config G c)} (p:Y ⊆ W):Arbor Y K I n C:=fun i u=> h _ (p u)
lemma cup_sum(h: Arbor W K I n C){R: α→ Config G c→ N}(p:Arbor W R I n D): Arbor W (fun i t=>K i t+ R i t) I n (C+D) := by
    intro u v i; obtain ⟨hh,ht⟩:=h _ v i; obtain ⟨hs,hp⟩:=p _ v i
    exact ⟨(hh.duo hs).move (V:=fun _ (y:N×N)=> (y.1:N)+y.2) (Warm.simple _ (contDiff_fst.add contDiff_snd|>.contDiffAt)), ht.add hp⟩
lemma cupL(h: Arbor W K I n C){R:α→ Config G c→ E}(L:N→L[ℝ] E→L[ℝ]H)(p:Arbor W R I n D): Arbor W (fun i t=>L (K i t) (R i t)) I n (2^n*‖L‖*C*D):=by
 intro u v i; obtain ⟨hh,ht⟩:=h _ v i; obtain ⟨hs,hp⟩:=p _ v i; exact ⟨(hh.duo hs).move (V:=fun _ (y:N×E)=>L y.1 y.2) (Warm.simple _ ((L.contDiff.comp contDiff_fst).clm_apply contDiff_snd|>.contDiffAt)), ht.bilinear L hp le_rfl⟩
end charge
end Arbor
end YM.CF.Forge
