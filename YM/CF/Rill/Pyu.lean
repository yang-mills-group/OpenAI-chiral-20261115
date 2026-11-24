import YM.CF.Rill.Tax
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Atala
variable {n:Side}{α: Type}[MeasurableSpace α]
open Cube Rush
variable {S:StepData (More c) (More f)} {T:Tube G S}{Y:Support (More f)} {E F D: Support (More c)}{M N: Monk G S}{m r:ℕ}
-- pay meas patched field at boundary still allowed.Support S.Template FeeR ν.V.P seen.F.Prop need Mask field Y.F.Meas on Support *only*.
lemma u_chop (X:Support (More c))(P:α→ Pane c)(S:α→ Ids c)(V:Loom c)(h:Roof c e t r V)(p:∀ a,halo (2*r+20) (flags e (P a)∩ E) ⊆ E)(g:halo r X⊆ E)(hp:∀ i:Bond (More c), i.1∈halo 12 E→ Measurable fun y=>P y i)(hq:Measurable S)(i:Bond (More c))(hg: Skye.ends i⊆ X): Measurable fun a=>V (P a,S a) i:=by
 let W(x)(i:Bond (More c)):= if i.1∈ halo 12 E then P x i else 1; have hv:Measurable W:=measurable_pi_lambda _ fun i=>by unfold W; split; exact hp _ ‹_›; exact measurable_const
 have he(a:α):V (P a,S a) i=V (W a,S a) i:=by
    have hu:Agrees (halo 12 E) (P a) (W a):=fun i p v=>(if_pos p).symm; have hs:=news (P a) (W a) e (Subset.refl _) hu -- infer
    exact (h.transmission _ _ _ _ E X (news _ _ _ (Subset.refl _) hu) (keepsL _ _ _ _ (p a) g) (keepsL _ _ _ _ (by rw [inter_comm (flags ..),←hs,inter_comm]; exact p a) g) (agrees_mono hu (halo_subset ..)) (fun _ _=>rfl)) i (hg (by simp)) (hg (by simp))
 rw [funext (g:=fun x=>V (W x,S x) i) he]; exact (measurable_pi_apply i).comp (h.bill.comp (hv.prodMk hq))
lemma pmeas{L N:Type}[MeasurableSpace L][TopologicalSpace L][BorelSpace L][MeasurableSpace N][TopologicalSpace N][BorelSpace N][SecondCountableTopology N](P:α→ L)(g:L→N)(A:Set L)(p:∀ x,P x∈A)(hp:Measurable P)(h:∀ v∈ A,ContinuousAt g v):Measurable (g ∘ P):= by
 let f(x):A:=⟨P x,p x⟩; let G':= g ∘ ((↑):A→L); have he: Continuous G':=continuous_iff_continuousAt.mpr fun i=> ((h i i.property).comp continuousAt_subtype_val)
 exact he.measurable.comp (show Measurable f from hp.subtype_mk)
set_option synthInstance.maxSize 25000 in
lemma leg_m(P:α→ HomeL (More c) (More f))(p:Measurable P)(g:∀ i,MarkP M E x e b (P i) l m T q d)(i:Bond (More f))(u:S.ratio.parent i.1∈ halo 13 E): Measurable fun y=> legL M T x q d l (P y) i:=by
 apply pmeas P (fun y=> legL M T x q d l y i) {v|MarkP M E x e b v l m T q d} (fun y=>g y) p; intro v p; have hh:MarkP M E x e b v l m T q d:=p
 exact (SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (wet _ (hh.tea i u))
lemma mean_p(P:α→ HomeL (More c) (More f))(p:Measurable P)(g:∀ y, MarkP M E x e b (P y) l m T q d)(X:Loom f)(v: Roof f e t r X)(L:α→ Ids f)(l':Measurable L)(h:halo r Y ⊆ Passage S E)(hp: M.key.dome (17*radiusB x)⊆ E)(hv:r≤radiusB x)(ht:1000≤radiusB x)(i:Bond (More f))(hX:Skye.ends i⊆ Y): Measurable (fun a=>X (legL M T x q d l (P a),L a) i):=by
 let Z(a):=legL M T x q d l (P a); let fu(Q:HomeL (More c) (More f)):=MarkP M E x e b Q l m T q d; let A:Set (HomeL (More c) (More f)):= fu
 exact u_chop Y Z L X v (fun y=>copyW (g y).toPaneL hp hv ht) h (fun i v=> leg_m P p g i (mem_filter.mp (parent_hK E v) |>.2)) l' i hX
end YM.CF.Rill
