import YM.CF.Rill.Foil
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
open Atala Cube
variable {S: StepData (More c) (More f)} {E F X:Support (More c)}{M:Monk G S}{T:Tube G S}{A:Loom c}{A':Loom f}{U:Config G (More f)}{k k' m:ℕ}{P:HomeL (More c) (More f)}
-- any family varying ONLY within given α parameters. require Q.argument motion within.Free. Need directional local fixed identities eventual ALL.
lemma loomM {α:Type}[TopologicalSpace α]{y:α}(V:α→ HomeL (More c) (More f))(p: V y=P)(hp:∀ᶠ i in 𝓝 y,P.2.1=(V i).2.1)(hc:∀ᶠ i in 𝓝 y,Agrees (halo 12 (halo (4*radiusB x) M.key.flags)) P.1 (V i).1) (hv:ContinuousAt V y)(h:MarkP M E x e b P l m T q d)(ht:0< fiery G x S.patch.L)(g:fiery G x S.patch.L<e) (hr: Roof f e w k A')(hl:Roof c e t k' A)(hq:looseV x M r v (legL M T x q d l P))(hx:b<firstRadius G)(u: k+k'≤radiusB x)(he:1000≤ radiusB x)(hd:halo (k+k'+30) X ⊆ E)(hK:M.key.dome (5*radiusB x) ⊆ E)(i:Ids f)(j:Ids c):
 let U(a):=legL M T x q d l a
 let Y(a:HomeL (More c) (More f)):=A' (U a,i)
 let Z(a:HomeL (More c) (More f)):=A (a.1,j)
 ∀ᶠ a in 𝓝 y,(∀ z:Bond (More f),S.ratio.parent z.1∈X→ if z.1∈ halo (k+2) (Passage S M.key.place) then Y (V a) z= Y P z else Y (V a) z=U (V a) z)∧(∀ z:Bond (More c),z.1∈ X →if z.1∈halo (k'+2) M.key.flags then Z (V a) z=Z P z else Z (V a) z=(V a).1 z):=by
 intro U Y Z;  
 have hh : SeeW (U P) e (Passage S E) (Passage S M.key.place):= join_l (monkD M P) hq h.toPaneL g ht
 have hu:Tendsto V (𝓝 y) (𝓝 P):= by rwa [←p]
 have hg : ∀ᶠ a in 𝓝 y,SeeW (U (V a)) e (Passage S E) (Passage S M.key.place):=hu.eventually (cotton U (fun i v=> (SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr ((wet _ (h.tea i ((mem_filter.mp (parent_hK (S:=S) _ v)).2))))) hh)
 filter_upwards [hu.eventually (mead h hx),hg,hp,hc] with a p' g' pV hC
 refine ⟨fun z p=> ?_,fun z p=>?_⟩
 · have hI:= blink hr (U:=(U (V a),i)) (V:=(U P,i)) (flue (S:=S) (Y:=X) ((Corona.halo_mono (by omega : k+30 ≤ k+k'+30) (Subset.refl _)).trans hd) hK he (by omega)) (sav _ _ _ _ g') (sav _ _ _ _ hh) (forke _ _ pV.symm (by omega)) (fun _ _=>rfl) z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,p⟩)
   split; rw [if_pos ‹_›] at hI; exact hI; rw [if_neg ‹_›] at hI; exact hI.1
 have hI:= blink hl (U:=((V a).1,j)) (V:=(P.1,j)) (footJ X (k:=k') ((Corona.halo_mono (by omega : k'+10≤ k+k'+30) (Subset.refl _)).trans hd) ((Corona.halo_mono (by omega : 4*radiusB x≤ 5*radiusB x) (Subset.refl _)).trans hK) he (by omega)) (sav _ _ _ _ p'.stampK) (sav _ _ _ _ h.stampK) (fun i p l=>(hC _ p l).symm) (fun _ _=>rfl) _ p
 split; rw [if_pos ‹_›] at hI; exact hI; rw [if_neg ‹_›] at hI; exact hI.1
end YM.CF.Rill
