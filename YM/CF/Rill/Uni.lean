import YM.CF.Rill.Thane
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
variable {u C a s:ℝ}
open Jet Atala
abbrev Cash(d:ℕ)(e C:ℝ):ℝ:= C^d*e
lemma take_k (p:1≤C)(h:0≤e)(v:r≤l):Cash r e C≤ Cash l e C:=by unfold Cash; gcongr
lemma put_c(r:ℕ)(e C:ℝ):C*Cash r e C=Cash (r+1) e C:=by unfold Cash; rw [pow_succ']; ring
lemma fee {x:Site f}(F:Forest S.ratio) (g:Tree.leaf S.ratio x) : S.ratio.parent ((F.up x).used x).1=S.ratio.parent x:=by
 have hh:=F.stays x g; cases k:F.up x with| mk i d=> rw [k] at hh; cases d; rfl; simpa [Step.used,Step.vec,sub_eq_add_neg] using hh
lemma leanS {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G f)(X:E)(F:Forest S.ratio)(n:ℕ)(hp:1≤C)(hg:0 ≤ e)(t:Wind d (·*·) n C)(r:Wind d (fun i _=>i⁻¹) n C)(y:Site f)(P:Site c)(g:S.ratio.parent y=P)(hx:Cash (4*S.ratio.count.val+3) e C ≤ d)(z:∀ i:Bond f,S.ratio.parent i.1=P → Tender (fun v=>U v i) X e n): Tender (fun v=> F.foldAt (U v) y) X (Cash (F.height y+3) e C) n:=by
 induction y using Forest.hike.induct F with
 | case1 y k ih=>
   let Y:=F.up y; let b:=Y.used y; let i:=y+Y.vec; let f(v):=(F.foldAt (U v) i); let T'(v):=Y.read (U v) y; let B:= F.height i+3
   have h{j:ℕ}(p:j≤4*S.ratio.count.val+3):Cash j e C ≤ d:=(take_k hp hg p).trans hx
   have h₀:Cash 0 e C=e:=by simp [Cash]
   have hy:Tender T' X (Cash 1 e C) n:=by
      let g':= z b ((fee F k).trans g); unfold T' Step.read; split
      next x=> rw [← put_c 0 e C,h₀]; exact r.duty (H:=fun v=>U v b) ((le_of_eq h₀.symm).trans (h (by omega))) g' g'
      next x=> exact g'.bag ((le_of_eq h₀.symm).trans (take_k hp hg (by norm_num)))
   have hv:Tender f X (Cash B e C) n:=ih ((F.stays y k).trans g); have hB:=F.bound i
   have hh:Tender (fun x=> T' x|>Inv.inv) X (Cash B e C) n:=((r.duty (V:=X) (h (by omega)) hy hy)).bag (le_trans (le_of_eq (put_c ..)) (take_k hp hg (by unfold B; omega)))
   apply ((t.duty (h (by unfold B; omega)) hv hh).bag ((le_of_eq (put_c ..)).trans (take_k hp hg (by have h:=F.rise y k; change F.height i < _ at h; unfold B; omega)))).same (Eventually.of_forall fun a:E=>congrArg SU.group.mat (show F.foldAt (U a) i*(T' a)⁻¹=F.foldAt (U a) y from ?_)); rw [show F.foldAt (U a) i= F.foldAt (U a) y*T' a from (F.fold_step (U a) k).symm,mul_inv_cancel_right]
 | case2 x k=>
    have h: (fun v=> F.foldAt (U v) x)=fun (_:E)=>1:= funext fun v=>by rw [show x=S.ratio.embed (S.ratio.parent x) from Classical.not_not.mp k]; exact Forest.fold_root ..
    rw [h]; exact (Shake.holds (SU.group.mat 1)).bag (by unfold Cash; positivity)
end YM.CF.Rill
