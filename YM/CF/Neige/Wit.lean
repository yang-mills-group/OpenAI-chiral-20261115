import YM.CF.Neige.Hollow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows
variable {α β:Type} [Fintype α][Fintype β][DecidableEq α][DecidableEq β]
section generic
variable (O:ColorOrtho G α)(e:α ≃ β)(M:Matrix (β × G.ColorIndex) (β × G.ColorIndex) ℝ) (P: ℝ→ Matrix (β × G.ColorIndex) (β × G.ColorIndex) ℝ)
local notation "L"=> warp O e
lemma ortz(t:ℝ): edgeM (L M) t=L (edgeM M t):=by unfold edgeM AnalyticNext.ConnectedActivity.ResolventVolume.graph; rw [add_w, one_w,scal_w]
lemma pivotB(n:ℕ)(p:Run α (n+1)):barP (L M) (L ∘ P) p=barP M P (e∘p):=by
 apply setIntegral_congr_fun measurableSet_Icc; intro t ht
 dsimp only [tileX]; rw [show linkX n (L M) ((L ∘ P) t) t=(fun i=> L (linkX n M (P t) t i)) from ?_, closing]
 funext i; cases i using Fin.cases with
 | zero=> exact (mul_w O e _ _).symm
 | succ j=> simp only [linkX,Fin.cons_succ, ortz,Function.comp_apply, Char.warp_subX,one_w,mul_w]
end generic
variable {q:Chi}{D m v' v'' X:ℝ} {L: Box x A A' F F'}{O:ColorOrtho G (Bond f)}{U: ColorOrtho G (Slots S)}(a:Flow L O U k k' T V W q D Y Y')
local notation "Q"=> warp (onBond O) L.onKey
include a
lemma letter_edge(p:Run (Active A' x F') (n+1)) : barP (emptyA T x k' A' F' W) (perZ T x k' A' F' W) p=barP (emptyA T x k A F V) (perZ T x k A F V) (L.onKey∘p):=by
 let M:= emptyA T x k A F V; have he: emptyA T x k' A' F' W= Q M:=by unfold emptyA M; rw [show baseX T x A' F' k' W=_ from a.test.kernel.same]; simp_rw [emptyA,Char.warp_subX,one_w]  -- tune
 have hx:perZ T x k' A' F' W= Q ∘ (perZ T x k A F V):=by
    funext t; unfold perZ stepM; rw [he,ortz]; unfold Function.comp pie; simp only [zero_smul,add_zero]; apply warp_per (w:=endLinks A' F' x); intro i; ext j; change meeting S x (L.onKey i.1).val.val (L.onKey j.1).val.val↔meeting S x i.1.val.val j.1.val.val; rw [L.atK,L.atK]; exact L.pane _ _
 rw [he,hx, pivotB]
lemma letterZ{m v b x': ℝ}(hp: FreeResolvent.Gap (baseX T x A F k V) m)(hL:120 ≤ radiusB x)(hm:0< m)(h: Flows L)(l:ℕ)(hs:S.patch.Branches S.kernel G)(hP:T.up.Bounds T.high v b x')
 (p:Run (Active A' x F') (n+1)): barP (neo T x k' A' F' W) (fun _=>1) p=barP (neo T x k A F V) (fun _=>1) (L.onKey∘p) ∧barP (acc T x k' A' F' q D Y' l W) (fun _=>1) p=barP (acc T x k A F q D Y l V) (fun _=>1) (L.onKey∘p):=by -- WRONG d different!
 let M:=neo T x k A F V; let N:=acc T x k A F q D Y l V
 have hx: bankX T x A' F' k' q D Y' l W= Q (bankX T x A F k q D Y l V):=by unfold bankX; rw [show bedX T x A' F' k' W=Q (bark x V T k A F) from boxH a hp hm hL, show majorX T x A' F' k' q D Y' l W=Q (hessN T x V k A F q D Y l) from boxV a h hs hP l]; rw [bank_w]
 have ht:acc T x k' A' F' q D Y' l W = Q N:= by
    dsimp only [N,acc]; dsimp only [Function.comp_apply]; rw [hx]; let V₁:=bankX T x A F k q D Y l V
    have h₁:=bill_w (onBond O) L.onKey (bankX T x A F k q D Y l V)
    unfold port at h₁; rw [add_w,one_w] at h₁; exact (add_left_cancel h₁).symm
 have hm':neo T x k' A' F' W=Q M:= by
    change perturb (bark x W T k' A' F') (baseX T x A' F' k' W)= Q (perturb (bark x V T k A F) _); rw [boxH a hp hm hL]; unfold baseX; rw [a.test.kernel.same,bank_w]
 have hu:(fun _ : ℝ=> (1:Shelf _))= Q ∘ (fun _ =>1):=by ext1; exact (one_w ..).symm
 rw [hm',ht,hu,pivotB,pivotB]; exact ⟨rfl,rfl⟩
end YM.CF.Neige
