import YM.CF.Forge.Out
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
variable {A F E H α:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup H][NormedSpace ℝ H][TopologicalSpace α]
abbrev TA := ℕ
structure Warm (F':α→ E→F)(n:TA)(p:α×E):Prop where
 lit : ∀ᶠ u:α×E in 𝓝 p, ContDiffAt ℝ (↑n) (F' u.1) u.2
 light (i:TA) (v:i≤n): ContinuousAt (fun x:α×E=> iteratedFDeriv ℝ i (F' x.1) x.2) p
namespace Warm
variable {M N:α→E→ F}{P:α→E→H}{n i:ℕ}{p:α×E}
lemma simple (L:E→F)(h:ContDiffAt ℝ (↑n) L p.2):Warm (fun _=> L) n p:= ⟨continuousAt_snd.tendsto.eventually (h.eventually (by simp)),fun i hi=> (h.continuousAt_iteratedFDeriv (Nat.cast_le.mpr hi)).comp continuousAt_snd⟩
lemma measured (L:α→ F)(h:ContinuousAt L p.1):Warm (fun t _=>L t) n p :=by
 refine ⟨Eventually.of_forall fun x=> contDiffAt_const,fun i hi=>?_⟩; cases i; swap; · simp_rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]; exact continuousAt_const
 simp_rw [iteratedFDeriv_zero_eq_comp]; exact ((continuousMultilinearCurryFin0 ℝ E F).symm.continuousAt.comp (h.comp continuousAt_fst))
lemma today (h:Warm M n p):ContDiffAt ℝ (↑n) (M p.1) p.2:= h.lit.self_of_nhds
lemma are(h:Warm M n p):ContinuousAt (uncurry M) p:=by
 let L' :=continuousMultilinearCurryFin0 ℝ E F; have hb:= L'.continuousAt.comp (h.light 0 (Nat.zero_le n)); unfold L' at *; simpa only [comp_def,uncurry_def,iteratedFDeriv_zero_eq_comp,LinearIsometryEquiv.apply_symm_apply] using hb
lemma duo (h:Warm M n p)(v:Warm P n p):Warm (fun x t=> (M x t,P x t)) n p:=by
 refine ⟨(h.lit.and v.lit).mono fun _ p=>p.1.prodMk p.2,fun i hv=>?_ ⟩; apply ((ContinuousMultilinearMap.prodL ℝ _ _ _).continuousAt.comp ((h.light i hv).prodMk (v.light i hv))).congr_of_eventuallyEq -- tune
 filter_upwards [h.lit,v.lit] with x hx hp; exact iteratedFDeriv_prodMk hx hp (Nat.cast_le.mpr hv)
lemma orbitM {ι:Type*}[Fintype ι]{A:ι→Type*}[∀ i, NormedAddCommGroup (A i)][∀ i,NormedSpace ℝ (A i)]{u:α→ ContinuousMultilinearMap ℝ A E}{m:α→∀ i,A i}{p:α}(h:ContinuousAt u p)(v:ContinuousAt m p) : ContinuousAt (fun x=>u x (m x)) p:=by
 let g(x):= (u x-u p) (m x); let L(x:α):=‖u x-u p‖ *∏ i, ‖m x i‖; have ht:ContinuousAt L p:= (h.sub continuousAt_const).norm.mul ((show Continuous (fun x : ∀ i,A i=> ∏ i,‖x i‖) from by fun_prop).continuousAt.comp v) -- check
 have hb: L p=0:=by simp [L]
 have hh:Tendsto (fun x=>‖g x‖) (𝓝 p) (𝓝 0):= squeeze_zero (fun _ => norm_nonneg _) (fun x=>ContinuousMultilinearMap.le_opNorm _ _) (hb ▸ ht) -- hb cast
 have hg:g p=0:=by simp [g]
 have hp:ContinuousAt g p:= by unfold ContinuousAt; rw [hg]; exact tendsto_zero_iff_norm_tendsto_zero.mpr hh
 have hv : ContinuousAt (fun x=>g x +u p (m x)) p:=hp.add ((u p).cont.continuousAt.comp v); simpa [g] using hv
lemma move {V:α→F→H} (h:Warm M n p)(v:Warm V n (p.1,M p.1 p.2)):Warm (fun i=> V i∘ M i) n p:=by
 let X(x:α×E):=(x.1,M x.1 x.2); have ht: ContinuousAt X p:= continuousAt_fst.prodMk h.are -- tune
 have he := ht.tendsto.eventually v.lit; -- may inference
 refine ⟨(he.and h.lit).mono (fun i r=> ?_),fun i hv=>?_ ⟩
 · exact r.1.comp i.2 r.2
 let P(z:OrderedFinpartition i)(x: α×E):= z.compAlongOrderedFinpartition (iteratedFDeriv ℝ z.length (V x.1) (M x.1 x.2)) (fun j=>iteratedFDeriv ℝ (z.partSize j) (M x.1) x.2)
 have hz(z):ContinuousAt (P z) p:= orbitM (α:=α×E) (u:=fun x=>(z.compAlongOrderedFinpartitionL ℝ E F H) (iteratedFDeriv ℝ z.length (V x.1) (M x.1 x.2))) (m:=fun x j=>iteratedFDeriv ℝ (z.partSize j) (M x.1) x.2) ( (z.compAlongOrderedFinpartitionL ℝ E F H).continuous.continuousAt.comp ((v.light z.length (z.length_le.trans hv)).comp (f:=X) ht)) (continuousAt_pi.mpr fun j=>h.light _ ((z.partSize_le j).trans hv))
 have hZ (t:Finset (OrderedFinpartition i)): ContinuousAt (fun x=>∑ z∈t,P z x) p:=by induction t using Finset.induction_on with | empty=>simpa using (show ContinuousAt (fun x:α×E=> (0:E [×i]→L[ℝ] H)) p from continuousAt_const) | insert d t u ih=>simp_rw [sum_insert u]; exact ((hz d).add ih) -- tune simpa
 apply (hZ univ).congr_of_eventuallyEq; filter_upwards [h.lit,he] with i' hi he; exact iteratedFDeriv_comp (f:=M i'.1) he hi (Nat.cast_le.mpr hv)
lemma together {g:E×F→ H}{x:E×F}(h:ContDiffAt ℝ (↑n) g x): Warm (fun i f=>g (i,f)) n x:=by
 let A:=fun i:TA=>ContinuousMultilinearMap.compContinuousLinearMapL (F:=H) (fun _ :Fin i=>ContinuousLinearMap.inr ℝ E F)
 have hh(z:E×F)(m:ContDiffAt ℝ (↑n) g z): ContDiffAt ℝ (↑n) (fun t=>g (z.1,t)) z.2∧∀ i:TA,i≤n → iteratedFDeriv ℝ i (fun t=>g (z.1,t)) z.2=A i (iteratedFDeriv ℝ i g z):=by
    let V:= ContinuousLinearMap.inr ℝ E F; let P(i:E×F):= g ((z.1,(0:F))+i); have hp : (z.1,(0:F))+V z.2=z:=by simp [V]
    have hv : ContDiffAt ℝ (↑n) P (V z.2):= ((show (z.1,(0:F))+V z.2=z from hp).symm ▸ m).comp (f:=fun i=> (z.1,(0:F))+i) (V z.2) (contDiffAt_const.add contDiffAt_id)
    rw [show (fun t=>g (z.1,t))=P ∘ V from funext fun v=> by dsimp [P,V]; simp]; refine ⟨hv.comp z.2 V.contDiff.contDiffAt,fun i p=>?_⟩; rw [Push.Uniform.iter_lin_at (hv.of_le (Nat.cast_le.mpr p))]; unfold P; rw [iteratedFDeriv_comp_add_left,hp]; rfl
 have hv:= h.eventually (by simp); refine ⟨hv.mono (fun x h=> (hh x h).1),fun i p=>?_⟩; exact ((A i).continuous.continuousAt.comp (h.continuousAt_iteratedFDeriv (Nat.cast_le.mpr p))).congr_of_eventuallyEq (hv.mono fun x h=> (hh x h).2 _ p)
lemma part (h:Warm M n p)(q:uncurry M=ᶠ[𝓝 p] uncurry N):Warm N n p:=by
 have he(x:α×E)(l:uncurry M=ᶠ[𝓝 x] uncurry N):M x.1 =ᶠ[𝓝 x.2] N x.1:= (show ContinuousAt (fun i:E=> (x.1,i)) x.2 from continuousAt_const.prodMk continuousAt_id).tendsto.eventually l
 have hh:= (eventually_eventually_nhds.mpr q).mono he
 refine ⟨(h.lit.and hh).mono fun x p=>p.1.congr_of_eventuallyEq p.2.symm,fun i v=>?_⟩; apply (h.light i v).congr_of_eventuallyEq; filter_upwards [hh] with x hx; exact (hx.iteratedFDeriv ℝ i).symm.self_of_nhds
end Warm
end YM.CF.Forge
