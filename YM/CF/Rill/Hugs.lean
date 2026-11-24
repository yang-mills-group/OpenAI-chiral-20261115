import YM.CF.Rill.Uni
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
open Jet Atala Cube Rush
variable {C u:ℝ}
variable {S:StepData (More c) (More f)} {K':Ratio c f}
lemma rills {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](W:E→ Pane c)(U:E→ Pane f)(X:E)(F:Forest (ratio K'))(n:ℕ)(p:1≤C)(h:0 ≤ e)(t:Wind d (·*·) n C)(v:Wind d (fun i _=>i⁻¹) n C)(hg:Wind d (knit q b) n C)(hp:S.ratio=ratio K')(y: Bond (More f))(u:Cash (4*S.ratio.count.val+13) e C≤d)(hc:Tender (fun i=> W i (S.ratio.parent y.1,y.2)) X e n)(z:∀ i:Bond (More f),separation (S.ratio.parent y.1) (S.ratio.parent i.1)≤1 →Tender (fun v=>U v i) X e n): Tender (fun v=> seine K' F q b (U v) (W v) y) X (Cash (4*S.ratio.count.val+13) e C) n:=by
 let R:= S.ratio; let I:Forest S.ratio:= hp.symm ▸ F; let B:= 4*S.ratio.count.val+3
 have hx(i:Site (More f))(g:separation (R.parent y.1) (R.parent i) ≤ 1) : Tender (fun u=>F.foldAt (U u) i) X (Cash B e C) n:=by
    have hz(u):I.foldAt (U u) i= F.foldAt (U u) i:=by
       have he(Gv Gr:Ratio (More c) (More f))(F: Forest Gr)(g:Gv=Gr): let I: Forest Gv:=g.symm ▸ F; I.foldAt (U u) i= F.foldAt (U u) i:=by subst Gr; rfl
       exact he _ _ F hp
    rw [← funext (g:=fun u=> F.foldAt (U u) i) hz]; exact (leanS (S:=S) U X I n p h t v i (R.parent i) rfl ((take_k p h (by omega)).trans u) (fun j h=> z j (h.symm ▸ g))).bag (take_k p h (Nat.add_le_add_right (I.bound i) _))
 have hA(j:ℕ)(p':j≤10):Cash (B+j) e C≤ d:=(take_k p h (by unfold B; omega)).trans u
 have hK:= hx y.1 (by simp)
 have hM:=hx (y.1+step y.2) (Work.E03.parent_step S y.1 y.2)
 let a:=fun i=>F.foldAt (U i) y.1; let aa:=fun i=>F.foldAt (U i) (y.1+step y.2)
 have hs:e≤Cash B e C:=(by simp [Cash] : e≤Cash 0 e C).trans (take_k p h (by omega)); let f(i):= Precision.replica (ratio K') (W i) y; let g(i):=Lattice.gauge (F.foldAt (U i)) (U i) y
 have he:Tender f X (Cash B e C) n:=by
    unfold f; rw [←hp]; unfold Precision.replica; split; exact (Shake.holds (SU.group.mat 1)).bag (h.trans hs); exact hc.bag hs
 have hm(q r:E→ SU.E)(i:ℕ)(v':i≤10)(z:Tender q X (Cash (B+i) e C) n)(g:Tender r X (Cash (B+i) e C) n): Tender (fun a=> q a*r a) X (Cash (B+i+1) e C) n:=by rw [←put_c]; exact t.duty (hA _ v') z g
 have hu:Tender (fun i=> (aa i)⁻¹) X (Cash (B+1) e C) n:=by rw [←put_c]; exact v.duty (hA 0 (by omega)) hM hM
 have hy: Tender (fun i=>(a i)⁻¹) X (Cash (B+1) e C) n:=by rw [←put_c]; exact v.duty (hA 0 (by omega)) hK hK
 have hh:Tender g X (Cash (B+2) e C) n:= hm _ _ 1 (by omega) (hm a (fun i=>U i y) 0 (by omega) hK ((z _ (by simp)).bag hs)) hu
 let C'(i):=portU K' F q b (U i) (W i) y; have hh:Tender C' X (Cash (B+3) e C) n:=by change Tender _ _ (Cash (B+2+1) e C) _; rw [←put_c]; exact hg.duty (hA _ (by omega)) hh (he.bag (take_k p h (by omega)))
 have hx:=hm (fun i=>(a i)⁻¹) C' 3 (by omega) (hy.bag (take_k p h (by omega))) hh
 have hW:Tender (fun i=> ((aa i)⁻¹)⁻¹) X (Cash (B+4) e C) n:=by simp only [inv_inv]; exact hM.bag (take_k p h (by omega))
 exact (hm _ _ 4 (by omega) hx hW).bag (take_k p h (by unfold B; omega))
end YM.CF.Rill
