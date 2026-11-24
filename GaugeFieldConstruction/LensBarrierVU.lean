import GaugeFieldConstruction.BarrierPathsVU
import GaugeFieldConstruction.VerdantΛL
/-! # On actual spacelike pair, local W value and its continuity & Eu Hart approach. -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Mink MeasureTheory Analysis Kernel Complex Metric Distribution
open scoped BigOperators Topology ContDiff InnerProductSpace
open NSF.Work.C20 NSF.LD
variable {G:Gauge}{L:Register G}{S T:Table L}{Y:Surface S}{D:∀ i,Blanket i}{F:Waves S}{A:Y.Aurora D}
variable (h:A.FullBody F){M: DiffPlan S}{R:S.Rotation}{s:S.RealSpin}{K:Spins S}
abbrev Gate2VU: NearPair 2:=⟨0,1,rfl⟩
lemma BarrierLetVU: Gate2VU.spectator 0 := by
 refine ⟨rfl,?_⟩; intro i j v d; fin_cases i <;> fin_cases j <;> simp_all [Gate2VU]
-- infrastructure Lore
include h
lemma StarsLampVU (q: K.Descends R s)(u:S.Symmetric)(e:M.Inclusions S)(X:LoreL F K Y T)(f:Fin 2→S.Union) : Nonempty (Gate2VU.Panes A f 0):=by
 obtain ⟨hp,he⟩:= Work.BarrierPathsVU.motionVU BarrierLetVU
 exact Work.C19.answer K Y D F A X.habitat h R s q M u e (Work.C18.answer _ _ _ q) (Work.C16.answer Y K D A F (glazeL D) X.habitat X.turns h) _ f Gate2VU 0 hp he
variable {n:ℕ}
omit h
lemma DawnLightVU: dawn (0:Heights n)=0:=by
 apply PiLp.ext; intro i; change position 0 0=(0:E4); apply Mink.ext_by <;> simp
include h
lemma clearVU {g:Fin 2→ S.Union}(M:Gate2VU.Panes A g 0)(q:Bid.cones Y)(x:Points 2)(v:x∈Gate2VU.gap):
 let C:= M.original x v; let V(y):=C.extendF (glow y (dawn (0:Heights 2)))
 ∃ (U:Set (Points 2)),IsOpen U∧ x∈U∧ ContinuousOn V U∧ ∀ f:Joint 2, HasCompactSupport ⇑f→ tsupport ⇑f⊆U→ Y.W 2 g f=∫ y,V y*f y:=by
 dsimp only
 obtain ⟨r,e,t⟩:=(Work.C21.answer F Y D A (glazeL D) h 2 g 0 Gate2VU M).body x v
 let C:= M.original x v; obtain ⟨i,k,w,z⟩:= C.revive
 let G(y:Points 2):= glow y (dawn (0:Heights 2)); have hg:Continuous G:= (home 2).comp (continuous_id.prodMk continuous_const)
 refine ⟨G ⁻¹' ball _ i ∩ ball x r,(isOpen_ball.preimage hg).inter isOpen_ball,⟨mem_ball_self k,mem_ball_self e⟩,w.continuousOn.comp hg.continuousOn (fun _ h=>h.1),fun f hp v=>?_⟩
 have hx:= t f hp (v.trans inter_subset_right); convert hx using 1
 rw [DawnLightVU,(D 2).flatD (glazeL D 2) (q _ _)] -- maybe tactic
-- general comparison of Pane and smooth
variable {x:Points 2}(ax:x∈conf 2)
variable (p:readings x=(0: Heights 2))
omit h
include p
lemma EtherVU:wickSlice 2 x=glow x (dawn (0:Heights 2)):=by
 rw[wick_glow,p]; congr; rw [← p, place_same] -- tune
lemma akinVU (g:Fin 2→S.Union)(K:Gate2VU.Panes A g 0)(i:x∈Gate2VU.gap)
 (E:Points 2→ℂ)(u:ContinuousAt E x)(t:EqOn (A.emit g ∘ wickSlice 2) E (ordered 2)): let T':=K.original x i; T'.extendF (glow x (dawn 0))=E x:=by
 dsimp only
 let M:=wickSlice 2; let N:=glow x (dawn (0: Heights 2)); let C:=K.original x i
 have he:Tendsto M (𝓝[ordered 2] x) (𝓝[tube 2] N):=by unfold N; rw [← EtherVU p]; exact M.continuous.continuousWithinAt.tendsto_nhdsWithin wick_tube
 haveI: (𝓝[ordered 2] x).NeBot:= ordered_neBot (p.symm ▸ light 2) -- tune
 exact tendsto_nhds_unique_of_eventuallyEq (C.doc.continuousAt.continuousWithinAt.tendsto.comp he) u.continuousWithinAt ((show C.extendF ∘ M =ᶠ[𝓝[ordered 2] x] A.emit g ∘ wickSlice 2 from he.eventually C.fits).trans (t.eventuallyEq_of_mem self_mem_nhdsWithin)) -- cast inference
#print axioms StarsLampVU
#print axioms akinVU
#print axioms clearVU
end YM.NSF.Boundary
end
