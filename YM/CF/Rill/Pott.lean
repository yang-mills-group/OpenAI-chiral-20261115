import YM.CF.Rill.Sell
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
attribute [local instance] opCStarAlgebra
open Cube Lat Acorn
variable {m B:Side}{p C:ℝ}
lemma walkL(S:Side) (U:Config G S) (hp:Guard U e)(h:e<b):∀ᶠ W in 𝓝 U,Guard W b:=by
 have hs(A:Type)[DecidableEq A][Fintype A](T:SU.E→* UNI A)(g: Continuous fun v=>(T v).val)(k:PlaqBound T U e):∀ᶠ W in 𝓝 U,PlaqBound T W b:=by
    have hp(i:Site S)(j:Axis)(l:Axis):∀ᶠ W in 𝓝 U,j≠l→‖(T (travel W i (square j l))).val-1‖ ≤ b:=by
       by_cases u:j=l; exact Eventually.of_forall fun _ p=> (p u).elim
       let f(W:Config G S):=‖(T (travel W i (square j l))).val-1‖; have hx: f U<b:=(k i j l u).trans_lt h; have hw: Continuous f:=((g.comp (show Continuous (fun W:Config G S=> travel W i (square j l)) from by fun_prop)).sub continuous_const).norm
       exact (hw.continuousAt.tendsto.eventually (gt_mem_nhds hx)).mono fun y h _=> LE.le.trans (LT.lt.le h) le_rfl -- tune travel matter st
    exact (eventually_all.mpr fun i=> (eventually_all.mpr fun j=>eventually_all.mpr fun l=>hp i j l))
 have hf:=hs _ firstF SU.fund_cont hp.1; exact hf.and (hs _ _ SU.matter_cont hp.2)
variable {α F:Type}[NormedAddCommGroup α][NormedSpace ℝ α][NormedAddCommGroup F][NormedSpace ℝ F]{z:α}{S X:Finset (Skye.Seat (CSide m B))}
open Jet
lemma post_u(k:ℕ){U:α→ Pane c} {X:Support (More c)} (h:∀ i:Bond (More c),Skye.ends i⊆X→Allows k (fun t=>SU.fund (U t i)) z 1):
 let V(t:α): Pane c:=fun i=>if Skye.ends i⊆ X then U t i else U z i
 TransK k V z 1∧ContinuousAt V z:=by -- undecl z
 intro V; have hp:TransK k V z 1:=by
    intro i; unfold V; split; exact h _ ‹_›; exact allows_const z (CStarRing.norm_of_mem_unitary (SU.fund_U ..)).le
 refine ⟨hp,continuousAt_pi.mpr fun i=>(SU.fund_cont.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (hp i).smooth.continuousAt⟩ -- tune meas
private lemma priced(k:ℕ){U:α→ Pane c}(h:TransK k U z 1)(g:1<p):∀ᶠ t in 𝓝 z,TransK k U t p:=by
 have ht(i:Bond (More c)):∀ᶠ v in 𝓝 z, Allows k (fun y=>SU.fund (U y i)) v p:=by
    let f:=fun y=> SU.fund (U y i); have hp:=h i; have hs (j: Fin (k+1)):∀ᶠ t in 𝓝 z,‖iteratedFDeriv ℝ (j:ℕ) f t‖≤p:=(((hp.smooth.continuousAt_iteratedFDeriv (Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt))).norm).eventually (gt_mem_nhds ((hp.norm_le j (Nat.le_of_lt_succ j.isLt)).trans_lt g))).mono fun i v=> LE.le.trans (LT.lt.le v) le_rfl
    filter_upwards [eventually_all.mpr hs,hp.smooth.eventually (by simp)] with i hs g; exact ⟨g,fun j v=>hs ⟨j,Nat.lt_succ_of_le v⟩⟩
 exact eventually_all.mpr ht
lemma cap_val [FiniteDimensional ℝ α](f: Castle m B b S→ ℂ)(k:ℕ)(U:α→ Castle m B b S)(z:α)(h: Acorn.Pro (landX k C S b) X f p)(g:e<b)(u:1<C)(hp:∀ i:Bool, Guard ((U z).val i) e)(hv:∀ i:Bool,∀ j:Bond (More (CSide m B)),Skye.ends j⊆X→Allows k (fun v=>SU.fund ((U v).val i j)) z 1):Allows k (f ∘ U) z p:=by
 let V(t:α)(i:Bool): Pane (CSide m B):=fun j=> if Skye.ends j⊆ X then (U t).val i j else (U z).val i j
 let W(t:α):=V t∈ MonoX m B b S; let F(t:α): Castle m B b S:=if h:W t then ⟨V t,h⟩ else U z
 have hJ:V z=(U z).val:=funext fun i=>funext fun k=>by simp [V]
 have hs: ∀ᶠ t in 𝓝 z,W t:=by
    have he(i):∀ᶠ t in 𝓝 z, Guard (V t i) b:= by
       refine ((show ContinuousAt (fun t=> V t i) z from (post_u k (U:=fun v=> (U v).val i) (hv i)).2)).eventually (p:=fun U=> Guard U b) ?_; change ∀ᶠ t in 𝓝 (V z i),Guard t b; rw [hJ]; exact walkL _ _ (hp i) g
    filter_upwards [eventually_all.mpr he] with t he; refine ⟨he,fun j v w=>?_⟩; unfold V; split; exact (U t).property.2 _ v w; exact (U z).property.2 _ v w
 have hh:∀ i:Bool,∀ᶠ t in 𝓝 z,TransK k (fun v=>(F v).val i) t C:=by
    intro i; have ht : (fun t:α=>(V t) i) =ᶠ[𝓝 z] fun t=>(F t).val i:= hs.mono fun i p=> by simp [F,p]
    filter_upwards [priced k (U:=fun v=> V v i) ((post_u _ (hv i)).1) u,eventually_eventually_nhds.mpr ht] with t l p; exact fun j=> (l j).germ (p.mono (fun y v=>congrArg SU.fund (congrFun v j)))
 obtain ⟨Y,hY,hf,hQ⟩:=_root_.mem_nhds_iff.mp (eventually_all.mpr hh); apply Allows.germ (h.plot α Y hf F (fun x hx=>hY hx) z hQ) -- tune
 filter_upwards [hs] with t v; apply h.reads (F t) (U t); intro i j p w; unfold F; rw [dif_pos v]; apply if_pos; exact insert_subset p (singleton_subset_iff.mpr w)
-- for compact caps & continuous local receipts
lemma project_meas{E F W X:Type}[TopologicalSpace E][CompactSpace E][TopologicalSpace F][T2Space F][MeasurableSpace F][BorelSpace F][MeasurableSpace X][TopologicalSpace W][MeasurableSpace W][BorelSpace W](U:E→ F)(f:E→ W)(W':X→ E)(p:Continuous U)(q:Continuous f)(h:∀ i j,U i=U j→ f i=f j)(hX:Measurable (U ∘ W')) : Measurable (f ∘ W'):=by
 apply measurable_of_isClosed; intro S v
 let T:Set F:= U '' (f ⁻¹' S); have hp:IsClosed T:= ((v.preimage q).isCompact.image p).isClosed
 rw [show (f ∘ W') ⁻¹' S = (U ∘ W') ⁻¹' T from ?_]; exact hX hp.measurableSet
 ext i; constructor; intro v; exact Set.mem_image_of_mem U v; intro v; obtain ⟨y,p,t⟩:=v; change f (W' i)∈ S; rw [←h _ _ t]; exact p
lemma pot_m(k:ℕ){U W} (p: Acorn.Pro (landX k C S b) X U W) {A:Type}[MeasurableSpace A](F:A→ Castle m B b S)(h:∀ (i:Bool) (j:Bond (More (CSide m B))),Skye.ends j⊆X→ Measurable (fun y:A=> (F y).val i j)) : Measurable (U∘ F):=by
 let Z:= {i: Bond (More (CSide m B))// Skye.ends i⊆ X}
 let g(W:Castle m B b S)(i:Bool)(j:Z):= W.val i j.val
 have hv(i:Bool)(j:Z):Continuous (fun x:Castle m B b S=>g x i j):=((continuous_apply j.val).comp (show Continuous (fun W:Castle m B b S=>W.val i) from (continuous_apply _).comp continuous_subtype_val))
 exact project_meas g U F (continuous_pi fun i=> continuous_pi fun j=> hv i j) p.cont (fun i j h=>p.reads _ _ (fun u b v k=>congrFun (congrFun h u) ⟨b,insert_subset v (singleton_subset_iff.mpr k)⟩)) (measurable_pi_lambda _ fun i=> measurable_pi_lambda _ fun j=>h i j.val j.property)
end YM.CF.Rill
