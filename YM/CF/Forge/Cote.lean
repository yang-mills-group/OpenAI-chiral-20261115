import YM.CF.Forge.Glen
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
variable {A F E H α:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup H][NormedSpace ℝ H][TopologicalSpace α] [MeasurableSpace α] [MeasurableSpace A] [MeasurableSpace F] [BorelSpace F][SecondCountableTopology F]
variable {f g:A→α→ Config G c→F}{V W Y:Set (Config G c)}{I:Finset (Bond c)}{X:Support c}{n:ℕ}{C D:ℝ}
def Gliss (V:Set (Config G c))(f:A→α→ Config G c→F):Prop:= Measurable fun i:A×α×Config G c=> V.indicator (f i.1 i.2.1) i.2.2 -- joint for integrations
lemma Gliss.low (h: Gliss V f)(u:W⊆ V)(p:MeasurableSet W): Gliss W f:=by
 unfold Gliss; rw [show (fun i:A×α×Config G c=> W.indicator (f i.1 i.2.1) i.2.2)={i:A×α×Config G c|i.2.2∈ W}.indicator (fun i:A×α×Config G c=> V.indicator (f i.1 i.2.1) i.2.2) from ?_]; swap; · funext i; by_cases hp:i.2.2∈ W<;> simp_all [Set.indicator]; exact fun x=>(x (u hp)).elim -- tune
 exact h.indicator ((measurable_snd.comp measurable_snd) p)
structure Locale (W:Set (Config G c))(f:A→α→ Config G c→F)(I:Finset (Bond c))(n:ℕ) :Prop where
 heat : IsOpen W
 joint : Gliss W f
 tel:∃ C:ℝ,0≤C∧∀ i,Arbor W (f i) I n C
namespace Locale
lemma loan (h: Locale V f I n)(u:W ⊆ V)(p:IsOpen W):Locale W f I n := ⟨p,h.joint.low u p.measurableSet, by obtain ⟨C,p,h⟩:=h.tel; exact ⟨C,p,fun i=>(h i).shrunk u⟩⟩
private lemma geist(h:MeasurableSet V) (hp:Gliss V f)(hW:Gliss W f):Gliss (V∪ W) f:=by
 unfold Gliss; convert! Measurable.ite ((measurable_snd.comp measurable_snd) h) hp hW using 1
 -- tune
 funext i; by_cases v:i.2.2∈ V <;> simp_all [Set.indicator]
 infer_instance
lemma un (h:Locale V f I n)(p:Locale W f I n):Locale (V∪W) f I n:=by
 refine ⟨h.heat.union p.heat,geist h.heat.measurableSet h.joint p.joint,?_⟩; obtain ⟨a,ha,h⟩:=h.tel; obtain ⟨b,hb,p⟩:=p.tel; refine ⟨max a b,le_max_of_le_left ha,fun i x v t=>v.elim (fun l=>(h i).cost_up (le_max_left a b) x l t) (fun l=> (p i).cost_up (le_max_right a b) x l t)⟩
lemma wideB (h:IsCompact Y)(u:∀ i∈Y,∃ V:Set (Config G c),i∈V∧ Locale V f I n): ∃ V :Set (Config G c),Y ⊆ V ∧ Locale V f I n:=by
 choose F k H using fun i:Y=>u i i.property
 obtain ⟨Z,h⟩:= h.elim_finite_subcover F (fun i=>(H i).heat) (fun x w=> Set.mem_iUnion.mpr ⟨_,k ⟨x,w⟩⟩)
 refine ⟨_,h,?_⟩; clear h; induction Z using Finset.induction_on with
 | empty=> simp only [Finset.notMem_empty,Set.iUnion_false,Set.iUnion_empty]; refine ⟨isOpen_empty,?_ ,⟨0,le_rfl,?_ ⟩⟩; unfold Gliss; simp only [Set.indicator_empty]; exact measurable_const; exact fun x V h=> (Set.notMem_empty _ h).elim
 | insert i Z l ih=> rw [Finset.set_biUnion_insert]; exact (H i).un ih
lemma cite (h:Locale W f I n)(p:∀ t x,Set.EqOn (f t x) (g t x) W):Locale W g I n:= ⟨h.heat,by unfold Gliss; have hx:=h.joint; unfold Gliss at hx; convert! hx using 1; funext i; by_cases u:i.2.2∈W; simp [Set.indicator_of_mem,u,(p i.1 i.2.1 u).symm]; simp [Set.indicator,u],by obtain ⟨C,p',u⟩:= h.tel; exact ⟨C,p',fun i=> (u i).part h.heat (p i)⟩⟩ -- tune
lemma envelope (X: Support c)(P:IsCompact Y)(H:Locale W f I n)(e:∀ U V:Config G c,Agrees X U V→U∈W→ V∈W)(l:Y⊆ W) (p:∀ i t,∀ U V:Config G c,Agrees X U V→ U∈ W → V∈ W →f i t U=f i t V) : ∃ g:A→α→ Config G c→F,Locale Set.univ g I n ∧(∀ U∈Y,∀ᶠ v in 𝓝 U,∀ i t,g i t v=f i t v)∧∀ i t, LocalOn X (g i t):=by
 obtain ⟨u,C,hC,hu,hy,hw,hx,Q⟩:= jaws (α:=α) X W ⟨_,H.heat,rfl⟩ P (fun i q _ v=> e _ _ v (l q)) I n
 let g(i:A)(t:α)(x:Config G c):F:=u x • f i t x; obtain ⟨L,hL,hT⟩:=H.tel
 let D:=(2:ℝ)^n*‖ContinuousLinearMap.lsmul ℝ ℝ (E:=F)‖*C*L
 refine ⟨g, ⟨isOpen_univ,?_,⟨D,(by unfold D; positivity),fun i U _ t=>?_⟩⟩,fun i p=> ?_,fun i t V Z he=>?_⟩
 · unfold Gliss; simp_rw [Set.indicator_univ]; have hz:Measurable (fun i:A×α× Config G c=> u i.2.2 • W.indicator (f i.1 i.2.1) i.2.2):= (hu.measurable.comp (measurable_snd.comp measurable_snd)).smul H.joint
   convert! hz using 1; funext i; by_cases p:i.2.2∈ W; · rw [Set.indicator_of_mem p] -- tune
   unfold g; rw [show u i.2.2=0 from (notMem_tsupport_iff_eventuallyEq.mp (fun w=> p (hw w))).self_of_nhds,zero_smul,zero_smul]
 · by_cases h:U∈ W
   · exact (Arbor.cupL (Q.shrunk (Set.subset_univ W)) (ContinuousLinearMap.lsmul ℝ ℝ) (hT i)) U h t
   have hh:∀ᶠ x in 𝓝 (0:Directions G c),u (gyrate I U x)=0:= (stickU I U).continuousAt.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp (fun w=>h ((born I U) ▸ hw w))) -- cast tune
   refine ⟨(Warm.simple (fun _=>0) contDiffAt_const).part ?_,(allows_const (v:=(0:F)) 0 (C:=D) (by rw [norm_zero]; unfold D; positivity)).germ (hh.mono (fun y p=> (show g i t _=0 from (by unfold g; rw [p,zero_smul])).symm))⟩
   filter_upwards [continuousAt_snd.eventually hh] with i p; simp only [g,uncurry,Function.comp_apply,p,zero_smul]; -- name shadow
 · filter_upwards [hx i p] with y t i j; simp [g,t]
 by_cases j:V∈ W
 · exact congrArg₂ (fun v x=> v • x) (hy _ _ he) (p i t V Z he j (e _ _ he j)) -- tune
 unfold g; rw [← hy _ _ he, show u V=0 from (notMem_tsupport_iff_eventuallyEq.mp (fun z=>j (hw z))).self_of_nhds]; simp
end Locale
end YM.CF.Forge
