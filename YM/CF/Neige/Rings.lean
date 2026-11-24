/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Neige.Fern
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymFare
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
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange Further.CurvedGaussianJets.Tracks
open PhysicalNext.OrderedAffine2B.SymFare
-- cap det logs incomes
variable {θ m U D v':ℝ}{q:Chi}
lemma earnX (h:Mem n T x θ C t s U F A k V l q D Y)(h₁:0<θ)(hC:0 ≤ C) (ht:t<1)(hp:s<1)(hh:C*tipPay θ x < 1):
 let A₀:=emptyA T x k A F V; let Q:=neo T x k A F V; let R:=acc T x k A F q D Y l V
 HasSum (fun i=> -(1/2:ℝ)*pulseX A₀ (perZ T x k A F V) i+(1/2:ℝ)*pulseX Q (fun _=>1) i +pulseX R (fun _=>1) i) (Real.log (layX T x A F k q D Y l V).det):=by
 intro A₀ Q R; have hv:Vmove x V 0=V:=by simp [Vmove]
 have hx:= (h.modes.paid 0 (by simp [Isle,interval])).1.nonneg; have hs:HasSum (pulseX R (fun _=>1)) (Real.log (1+R).det):=by
    unfold R; rw [←hv]; exact h.modes.run hx hp
 let K:=baseX T x A F k V; let T':=bedX T x A F k V
 have he:HasSum (pulseX A₀ (perZ T x k A F V)) (Real.log K.det):=by
    rw [show K=1+A₀ from (add_sub_cancel ..).symm]; unfold A₀; rw [←hv]; exact h.center.run (mul_nonneg hC (Real.exp_pos _).le) hh
 have hq: HasSum (pulseX Q (fun _=>1)) (Real.log (1+Q).det):=by
    unfold Q; rw [←hv]; exact h.core.run ((h.core.paid 0 (by simp [Isle,interval])).2.nonneg) ht
 have hp': IsUnit K.det:=by
    have he:= h.center.heart 1 (by simp [Isle,interval]); rw [Function.comp_apply, hv,edgeM,AnalyticNext.ConnectedActivity.ResolventVolume.graph,one_smul, emptyA,add_sub_cancel] at he; exact he
 have hT: layX T x A F k q D Y l V=T'*(1+R):=rfl; have hS:(layX T x A F k q D Y l V).det≠0:=h.vertex.ne_zero; rw [hT,Matrix.det_mul,mul_ne_zero_iff] at hS
 have hV:1+Q=T'ᵀ * K*T':=add_sub_cancel ..
 rw [hT,det_mul,Real.log_mul hS.1 hS.2]; have hf:=((he.mul_left (-(1/2:ℝ))).add (hq.mul_left (1/2:ℝ))).add hs
 rwa [show -(1/2:ℝ) * Real.log K.det+ (1/2:ℝ)*Real.log (1+Q).det=Real.log T'.det by rw [hV,det_mul,det_mul,det_transpose,Real.log_mul (mul_ne_zero hS.1 hp'.ne_zero) hS.1,Real.log_mul hS.1 hp'.ne_zero]; ring] at hf
section trail
variable {β:Type}[Fintype β][DecidableEq β]{k:ℕ}
def linkX (n:ℕ)(Q P: Shelf α) (t:ℝ): Fin (n+1)→ Shelf α:= Fin.cons (α:=fun _ : Fin (n+1)=>Shelf α) (Q*P) (fun _=>1-edgeM Q t*P)
def tileX(A:Shelf (α×β))(P:ℝ→Shelf (α×β))(w: Run α (k+1))(t:ℝ):= close w (fun v=> fare v (linkX k A (P t) t))
def barP(A:Shelf (α×β))(P:ℝ→Shelf (α×β))(w: Run α (k+1)):=∫ t in Isle,tileX A P w t
private lemma summed(M:Fin k→Shelf α):∑ p, (if p 0=p (Fin.last k) then fare p M else 0)=Matrix.trace (engine M):=by
 unfold Matrix.trace; simp_rw [Matrix.diag_apply,engine_entries]; rw [Finset.sum_comm]; refine sum_congr rfl fun p _=>?_ ; unfold ends; rw [sum_eq_single (p 0) (fun i _ hi=>if_neg (fun h=>hi h.1.symm)) (by simp)]
 simp [eq_comm]
lemma regard(A:Shelf (α×β))(P:ℝ→ Shelf (α×β))(k:ℕ)(t:ℝ): trace (grind A P k t)=∑ w, tileX A P (w: Run α (k+1)) t:=by
 let M:= linkX k A (P t) t; have ht: grind A P k t=engine M:=by unfold M linkX; rw [engine_next,Fin.cons_zero,Fin.tail_cons,engine_pow]; rfl
 rw [ht,← summed]; let E:= (Equiv.arrowProdEquivProdArrow (Fin (k+2)) (fun _=>α) (fun _=>β)).symm; rw [← E.sum_comp,Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ -- unfolding
 let u:= mix i j
 have he:u 0=u (Fin.last (k+1))↔ i (Fin.last (k+1))=i 0 ∧ j (Fin.last (k+1))=j 0:= by simp [u,mix,eq_comm]
 change (if u 0 = u _ then _ else _)= _; rw [if_congr he rfl rfl]; rfl
section loops
variable {A:E→ Shelf (α×β)}{P:E→ℝ→ Shelf (α×β)} {n k:ℕ}{x:E}
lemma fare_s(z:Run (α×β) (k+1))(h:PriceW A P n x C t): Arc (fun y:E × ℝ=> fare z (linkX k (A y.1) (P y.1 y.2) y.2)) n x:=by
 intro t' ht; unfold fare; apply contDiffAt_prod
 intro i hI; cases i using Fin.cases with
 | zero=>exact AnalyticBridge.RelativeLogdet.typed (h.St _ ht) _ _
 | succ j=> simp only [linkX,Fin.cons_succ]; exact AnalyticBridge.RelativeLogdet.typed (h.Tag _ ht) _ _
lemma tile_s(h:PriceW A P n x C t)(w:Run α (k+1)): Arc (fun y:E × ℝ=> tileX (A y.1) (P y.1) w y.2) n x:=by
 intro t' ht'; unfold tileX close; apply ContDiffAt.sum; intro i _; split
 next h'=> exact fare_s (mix w i) h t' ht'
 exact contDiffAt_const
lemma bS(h:PriceW A P n x C t)(k:ℕ): pulseX (A x) (P x) k=∑ w:Run α (k+1),barP (A x) (P x) w:=by
 unfold pulseX; simp_rw [regard]; rw [integral_finsetSum _ fun i _=> (tile_s h i).slice.integrableOn_Icc]; rfl
end loops
end trail
end YM.CF.Neige
