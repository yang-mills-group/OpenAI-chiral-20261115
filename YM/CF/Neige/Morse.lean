import YM.CF.Neige.Rings
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
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable {θ m U D v':ℝ}{q:Chi}
lemma oneCost_r{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{f g:E→ℝ}(h: Allows n f x C)(hp:Allows n g x K): Allows n (fun y=>f y*g y) x (2^n*C*K):=by
 have hh:= h.bilinear (ContinuousLinearMap.mul ℝ ℝ) hp (show ‖ContinuousLinearMap.mul ℝ ℝ‖≤1 from ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun i j=> by rw [one_mul]; exact norm_mul_le ..); rwa [mul_one] at hh
section paths
variable {β:Type} [Fintype β][DecidableEq β]{n k d:ℕ}{x:E}
-- common X independence stencil
lemma eat_r{f: Fin d→E→Matrix α α ℝ}{v:Fin d→ℝ}(p: Run α d)(h:∀ i,Protected n (f i) x (v i)): Allows n (fun x=>fare p (fun i=>f i x)) x (∏ i, (2^n*v i)):=by
 induction d with
 | zero=> simp_rw [fare_zero]; exact allows_const _ (by simp)
 | succ d ih =>
    simp_rw [fare_next]; let a:=p 0; let b:= Fin.tail p 0; let g (x:E):=f 0 x a b
    let H(z:E):= f 0 z
    have hp: Allows n g x (v 0):=by
        have hh:= h 0; apply (Char.cost_alt (g:=fun _=>0) (show Allows n (fun y=> paintO (H y)-paintO (0:Matrix α α ℝ)) x (v 0) by simp only [map_zero, sub_zero]; exact hh) a b).germ (Eventually.of_forall fun z=>sub_zero (H z a b))
    have he: ∀ i: Fin d,Protected n (Fin.tail f i) x (Fin.tail v i):=fun i=>h _
    exact (oneCost_r hp (ih (Fin.tail p) he)).mono (Fin.prod_univ_succ (fun i:Fin (d+1)=> 2^n*v i)).symm.le
variable {A:E→ Shelf (α×β)}{P:E→ℝ→ Shelf (α×β)}
lemma tile_cost(h:PriceW A P n x C t)(w:Run α (k+1))(t':ℝ)(ht:t'∈Isle):
 Allows n (fun y=>tileX (A y) (P y) w t') x ((Fintype.card β)^(k+1+1)*(2^n*C*(2^n*t)^k)):=by
 let v(i:Fin (k+1)):ℝ:= Fin.cons (α:=fun _=>ℝ) C (fun _=>t) i; let D':=2^n*C*(2^n*t)^k
 let f(i:Fin (k+1))(y:E):= linkX k (A y) (P y t') t' i
 have he(i):Protected n (f i) x (v i):=by
    induction i using Fin.cases with
    | zero=>exact (h.paid t' ht).1
    | succ i=> simp only [v,f,linkX,Fin.cons_succ]; exact (h.paid t' ht).2
 let F(i:Run β (k+1))(y:E):= if w (Fin.last (k+1))=w 0∧ i (Fin.last (k+1))=i 0 then fare (mix w i) (fun j=> f j y) else 0
 have hp(i): Allows n (F i) x D':=by
    have ht:=eat_r (mix w i) he; have hZ: (∏ j,2^n*v j) =D':=by rw [Fin.prod_univ_succ]; simp only [v, Fin.cons_succ,Fin.cons_zero, Finset.prod_const, Finset.card_univ,Fintype.card_fin]; rfl
    unfold F; split
    · exact ht.mono hZ.le
    exact allows_const x (by rw [norm_zero]; exact ht.nonneg.trans hZ.le)
 have hx:= Jet.allows_sum (s:=Finset.univ) (f:=F) (fun i _=>hp i)
 rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,show Fintype.card (Run β (k+1))=Fintype.card β^(k+1+1) by simp [Run],Nat.cast_pow] at hx; exact hx
lemma bar_t [FiniteDimensional ℝ E](h:PriceW A P n x C t)(w:Run α (k+1)):
 Allows n (fun y=>barP (A y) (P y) w) x ((Fintype.card β)^(k+1+1)*(2^n*C*(2^n*t)^k)):= spirit (tile_s h w) (tile_cost h w)
end paths
end YM.CF.Neige
