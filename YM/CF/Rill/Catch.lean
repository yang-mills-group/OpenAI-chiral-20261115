import YM.CF.Rill.Peer
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
-- local flag fun
variable {n:Side}
lemma news(U V: Config G c)(t:ℝ){X Y: Support c}(p:halo 12 X ⊆ Y)(h:Agrees Y U V) : X ∩ flags t U=X∩ flags t V:=by
 ext i; simp only [mem_inter,flags_spec]; apply and_congr_right; intro v; refine exists_congr fun j=>and_congr_right fun k=>?_; rw [show faceValue U j=faceValue V j from travel_local _ _ _ _ fun a u l=> h a (p (halo_spec.mpr ⟨i,v,terrain k (List.mem_toFinset.mpr u)⟩)) (p (halo_spec.mpr ⟨i,v,terrain k (List.mem_toFinset.mpr l)⟩))]
-- Template Week
open Cube
variable {S: StepData (More c) (More f)}{Y:Support (More c)}{M N:Monk G S}{E F: Support (More c)}{k k':ℕ}{U:Loom f}{C:Loom c}{T:Tube G S}{W:Config G (More f)}
lemma copyW (p:PaneL M E x e b W)(h: M.key.dome (17*radiusB x)⊆ E)(t:k ≤ radiusB x)(ht:1000≤radiusB x): halo (2*k+20) (flags e W∩Passage S E)⊆ Passage S E:=by
 -- eliminate unused ↑
 intro i d; obtain ⟨j,z,w⟩:=halo_spec.mp d; have hp:= (mem_filter.mp ((sav _ _ _ _ p.mindF) (show j∈ Passage S E∩ flags e W from ?_))).2; swap; · rwa [inter_comm]
 have hn:= Work.E04.parent_separation S.ratio j i; refine mem_filter.mpr ⟨mem_univ _, h (Atala.dome_u hp (by omega))⟩
lemma chimeW (p:Beat M N F)(g:Ready T x)(hp:1000≤radiusB x)(hz:halo ((l+70)*radiusB x) E⊆F): Agrees (halo 12 (Passage S E)) (M.sent x T q d l β) (N.sent x T q d l β):=by
 intro i u z; apply p.backF g hp i; have hk:= (mem_filter.mp (parent_hK E u)).2; intro y l; obtain ⟨q,h,p⟩:=halo_spec.mp hk; obtain ⟨r,w,j⟩:=halo_spec.mp l; rw [mem_singleton.mp w] at j; apply hz (halo_spec.mpr ⟨q,h,(separation_triangle q (S.ratio.parent i.1) y).trans ?_⟩); simp_rw [Nat.add_mul] at *; omega
lemma fieldR (p:PaneL M E x e b (M.sent x T q d l β))(h:Beat M N F)(g: Ready T x)(hp:1000≤ radiusB x)(hz:halo ((l+70)*radiusB x) E⊆F)(hs:Roof f e w k U)(hc: Roof c e t k' C)(hk:k+k' ≤ radiusB x)(v: M.key.dome (17*radiusB x)⊆ E)(Q:Support (More c))(K:Support (More f))(hZ:halo k K⊆ Passage S E)(hc':halo k' Q⊆ E)(a z:Ids c)(y i:Ids f)(he:Set.EqOn a z E)(hm:Set.EqOn y i (Passage S E)):
 Agrees K (U (M.sent x T q d l β,y)) (U (N.sent x T q d l β,i)) ∧ Agrees Q (C (M.V,a)) (C (N.V,z)):=by
 let X:= M.sent x T q d l β; let Y:= N.sent x T q d l β; let J:= Passage S E; have hw:Agrees (halo 12 (Passage S E)) X Y:=chimeW h g hp hz
 have hp':= news X Y e (Subset.refl _) hw -- tune X.F inferred J?
 have he':=copyW p v (by omega : k≤radiusB x) hp
 have hK:=hs.transmission X Y y i J K (news X Y e (Subset.refl _) hw) (keepsL _ _ _ k he' hZ) (keepsL _ _ _ k ?_ hZ) (agrees_mono hw (halo_subset ..)) hm; swap; · change halo _ (flags e Y ∩ (Passage S E)) ⊆_; rw [inter_comm,←hp',inter_comm]; exact he'
 have hu:halo 12 E ⊆ F:=Subset.trans (Corona.halo_mono (by simp_rw [Nat.add_mul]; omega : 12≤(l+70)*radiusB x) (Subset.refl _)) hz
 have h': (E∩ flags e M.V)=E∩ flags e N.V:= news _ _ _ hu h.view
 have hv:halo (2*k'+20) (flags e M.V∩E) ⊆ E:=by
    intro x hx; obtain ⟨a,t,h⟩:=halo_spec.mp hx; have hp':a∈M.key.flags:= (sav _ _ _ _ p.stampK) (by rwa [inter_comm]); exact v (halo_spec.mpr ⟨a,mem_union_right _ hp',by omega⟩)
 exact ⟨hK,hc.transmission M.V N.V _ _ E Q h' (keepsL _ _ _ _ hv hc') (keepsL _ _ _ _ (by rw [inter_comm (flags ..),←h',inter_comm]; exact hv) hc') (agrees_mono h.view ((halo_subset ..).trans hu)) he⟩
end YM.CF.Rill
