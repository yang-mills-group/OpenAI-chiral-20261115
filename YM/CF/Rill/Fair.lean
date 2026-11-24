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
open Atala Cube
variable {S: StepData (More c) (More f)}{Y:Support (More c)}{M N:Monk G S}{E F: Support (More c)}{k k':ℕ}{U:Loom f}{C:Loom c}{T:Tube G S}{X:Config G (More f)}
-- weakened at owner.Portal
lemma partR {i:Bond (More f)}(p:PaneL M E x e b X)(ht:Roof f e w k U)(hz:S.ratio.parent i.1 ∉ M.key.dome (19*radiusB x)) (hh:Beat.shadows (o:= S.ratio.parent i.1) E (k+5))(hv:k≤radiusB x)(hp:1000≤radiusB x)(Z:Ids f): U (X,Z) i=X i:=by
 apply ht.lamp _ _ _ (disjoint_left.mpr fun r t v=>?_)
 have hg:=Work.E04.parent_separation S.ratio r i.1; have hu := win_r v
 have he:separation (S.ratio.parent r) (S.ratio.parent i.1)≤k+5:=by omega
 have hw:r∈ Passage S E:=mem_filter.mpr ⟨mem_univ _,hh (halo_spec.mpr ⟨_,mem_singleton_self _,(separation_comm ..).trans_le he⟩)⟩; exact hz (Atala.dome_u ((mem_filter.mp (sav _ _ _ _ p.mindF (mem_inter.mpr ⟨hw,t⟩))).2) (by omega))
open Rush
private lemma warp_f (Gv:Forest S.ratio)(K: Ratio c f)(h:S.ratio=ratio K) (V:Config G (More f))(i:Site (More f)):Gv.foldAt V i=(show Forest (ratio K) from h ▸ Gv).foldAt V i:=by
 have hz(C C':Ratio (More c) (More f))(Y:Forest C)(p:C=C'): let X:Forest C':=p ▸ Y; Y.foldAt V i=X.foldAt V i:=by subst C; rfl
 exact hz _ _ _ h
set_option maxHeartbeats 1000000 in
lemma beam_l (K: Ratio c f)(h:S.ratio=ratio K) (q':Chi)(p:PaneL M E x e b (M.sent x T q d l β))(ht:Roof f e w k U)(hg: Roof c e t k' C)(hz:k+k'≤radiusB x)(hp:1000≤radiusB x)(hx:0<b)(hr:b<firstRadius G)(i:Bond (More f))(hu:S.ratio.parent i.1 ∉ M.key.dome (20*radiusB x))(hs:Beat.shadows (o:=S.ratio.parent i.1) E (k+k'+30))(A:Ids c)(Z:Ids f) :
 seine K (h ▸ M.park) q' b (U (M.sent x T q d l β,Z)) (C (M.V,A)) i= U (M.sent x T q d l β,Z) i:=by
 let F:=M.park; let W:=M.sent x T q d l β; let P:= U (W,Z); let C':= C (M.V,A); let H:Forest (ratio K):= h ▸ F; let o:=S.ratio.parent i.1; let R:=radiusB x
 have hh{j:Bond (More f)}(g:separation o (S.ratio.parent j.1)≤1):P j=W j:=by
    refine partR p ht (fun v=>hu (Atala.dome_u v ?_)) ?_ (by omega) hp Z
    · change _+separation _ o≤ _; rw [separation_comm]; omega
    exact Forge.aroundBk E hs (by change separation o _ +_ ≤_; omega)
 have hv(x:Site (More f))(k:separation o (S.ratio.parent x)≤1): H.foldAt P x=1:=by
    rw [←warp_f (S:=S) F K h P]; apply fills_l (S:=S) F P _ (fun j p t=> Eq.trans (hh (t.symm ▸ k)) (Atala.tipS _ p)) x rfl
 have h1:H.foldAt P i.1=1:=hv i.1 (by simp [o]); have h2:H.foldAt P (i.1+step i.2)=1:= hv _ (Work.E03.parent_step S i.1 i.2)
 have hc: P i=W i:= hh (by simp [o]); have hq:Precision.replica (ratio K) C' i=Precision.replica S.ratio M.V i:=by
    rw [←h]; unfold Precision.replica; split; rfl
    apply hg.lamp _ _ _ (disjoint_left.mpr fun y u t=>?_); have hk':separation y o ≤ k'+1:=win_r t
    have he : y∈ E:= hs (halo_spec.mpr ⟨o, mem_singleton_self _, (separation_comm ..).trans_le (hk'.trans (by omega))⟩); have hp':y∈ M.key.flags:=sav _ _ _ _ p.stampK (mem_inter.mpr ⟨he,u⟩); exact hu (halo_spec.mpr ⟨y,mem_union_right _ hp', hk'.trans (by omega)⟩)
 change seine K H q' b P C' i=P i; unfold seine portU Lattice.gauge; dsimp only [Pi.inv_apply]; rw [h1,h2,hc,hq]; simp only [inv_one,mul_one,one_mul]; apply knitHere _ _ _ _ hx hr; obtain ⟨z,hz,u⟩:= p.farF i (hs (halo_spec.mpr ⟨o,mem_singleton_self _,by simp [o]⟩)) hu; exact ⟨z, (mem_ball_zero_iff.mp hz).le,by rw [u, mul_assoc, inv_mul_cancel,mul_one]⟩
end YM.CF.Rill
