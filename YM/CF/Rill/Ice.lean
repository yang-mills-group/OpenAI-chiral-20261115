import YM.CF.Rill.Catch
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
-- U# Patch.S.For flagged markers near roots.Wings. X∀ any flags in region.L small. choose R=Support flags baseline region
variable {n:Side}
open Cube
variable {E L H D F:Support (More n)} {A:Loom n} {k:ℕ} {U V: Orbit n}
-- abstract holds under Edit:
structure IceK (A:Loom n)(E K L D:Support (More n))(k:ℕ)(e:ℝ) :Prop where
 hat: halo (k+10) E ⊆ K
 shock: L⊆ K
 flag: halo (2*k+20) D ⊆ L
lemma blink (p:Roof n e b k A)(h:IceK A E F L D k e)(g:F∩ flags e U.1 ⊆ D)(j:F∩ flags e V.1 ⊆ D)(s:Agrees (halo 12 L) U.1 V.1)(v:Set.EqOn U.2 V.2 L)(i:Bond (More n))(w:i.1∈E):
 -- condition branch fixed by anchor(i.1∈...)
 if i.1∈ halo (k+2) D then A U i=A V i else A U i= U.1 i ∧ A V i= V.1 i:=by
 have hu:win k i⊆ F:=by intro j p; apply h.hat; exact halo_spec.mpr ⟨i.1,w,(separation_comm ..).trans_le ((Atala.win_r p).trans (by omega)) ⟩
 split
 next hx=>
    have hr(U':Orbit n)(g:F∩ flags e U'.1 ⊆ D):Week L (ends i) (flags e U'.1) k:=by
       apply keepsL
       · exact Subset.trans (Corona.halo_mono le_rfl (show flags e U'.1∩L ⊆ D from fun z t=>g (mem_inter.mpr ⟨h.shock (mem_inter.mp t).2,(mem_inter.mp t).1⟩))) h.flag
       intro j t; obtain ⟨u,v,g⟩:=halo_spec.mp hx; apply h.flag; exact halo_spec.mpr ⟨u,v,(separation_triangle u i.1 j).trans (Nat.add_le_add g ((separation_comm i.1 j).trans_le (Atala.win_r t))|>.trans (by omega))⟩ -- precedence
    exact p.transmission _ _ _ _ L (ends i) (news _ _ e (Subset.refl _) s) (hr U g) (hr V j) (agrees_mono s (halo_subset 12 _)) v i (by simp) (by simp)
 next hx=>
    have hr(U':Orbit n)(g:F∩ flags e U'.1⊆ D) :A U' i=U'.1 i:=p.lamp _ _ _ (disjoint_left.mpr fun j t q=> hx (halo_spec.mpr ⟨j,g (mem_inter.mpr ⟨hu q,t⟩),(Atala.win_r q).trans (by omega)⟩))
    exact ⟨hr U g,hr V j⟩
end YM.CF.Rill
