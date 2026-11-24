import YM.CF.Neige.Say
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
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange Push
variable {d v' d' θ ρ m q' M:ℝ}
section
open FreeResolvent.TestD
abbrev emptyA(T:Tube G S)(x:ℝ)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(V:Config G c):=baseX T x A F k V-1
def perZ (T:Tube G S)(x:ℝ)(k:S.Choices)(A:Stores S)(F:Forest S.ratio)(V:Config G c):=stepM (panels A F) (emptyA T x k A F V)
lemma cap_tag(hp:Polar (G:=G) 0 (front (G:=G) (x:=x) A F) (front A F) (baseX T x A F k∘AnalyticBridge.SectorAffine.field V) n d C)(hB:FreeResolvent.Gap (baseX T x A F k V) m)(he:0< m)(hd:0<d)(h:120 ≤ radiusB x)(ht:temp x  ≤ 1)(hC:0  ≤  C)
 (hQ:Price d (C+1) (min m 1) d' 1 v' 1 n) (hV:(FreeResolvent.native c).Volume (front (G:=G) A F (x:=x)) d' v') :
 let L:=v'*FreeResolvent.TestD.meter n n (C+1) 1 (rise v' (min m 1)); let U₀:=FreeResolvent.tagPrice 1 n (C+1) L; let ε:=Real.exp (-(n+1:ℕ)*d'*(radiusB x/60:ℕ))
 let t:=Jet.composeCost n (activation G n 0 d*C) 1; let U:=Jet.composeCost n (activation G n 0 d'*L) 1
 PriceW (emptyA T x k A F∘Vmove x V) (perZ T x k A F ∘ Vmove x V) n 0 (2^n*(t+1)*U) (Jet.composeCost n (activation G n 0 d'*(ε*U₀)) 1):=by -- peak
 intro L U₀ ε t U
 let W:=baseX T x A F k; let R:=W ∘AnalyticBridge.SectorAffine.field V
 have hR:R 0=W V:=by simp [R,field_zero]
 have hπ:=boards A F G h; have hv:=per_self hπ; have hm:FreeResolvent.Gap (R 0) m:=hR.symm ▸ hB
 have hB:=tag_h hv hp hm he
 let P:=panels A F (G:=G) (x:=x); let X:Directions G c→L[ℝ] PriceCoords G c:= (reader G c).comp (temp x • ContinuousLinearMap.id ℝ _); let B:=Vmove x V
 have heB(y:Directions G c): R (X y)= W (Vmove x V y):= congr_arg W (reader_field ..)
 have hZ: Arc (uncurry (perZ T x k A F∘ B)) n 0:=by
    intro t hT
    let L(z:Directions G c×ℝ):=(X z.1,z.2); let H(z:PriceCoords G c×ℝ):=stepM P (R z.1-1) z.2
    have hz':L (0,t)=(0,t):=by simp [L]
    have hh:ContDiffAt ℝ n (H ∘ L) (0,t):=(show ContDiffAt ℝ n H (L (0,t)) by rw [hz']; exact hB t hT).comp _ ((X.contDiff.contDiffAt.comp (f:=Prod.fst) _ contDiffAt_fst).prodMk contDiffAt_snd)
    apply hh.congr_of_eventuallyEq; apply Eventually.of_forall; rintro ⟨y,t⟩; exact congr_arg (fun A=>stepM P (A-1) t) (heB y).symm
 have hW := warp_h (front A F) hp hd hC ht (g:=W); have hP: Protected n (emptyA T x k A F∘ B) 0 (t+1):=subsid hW (show Protected n (fun _:Directions G c=> (1: Shelf (Rows.In x A F (G:=G)))) 0 1 from allows_const _ (by rw [paint_one]; exact ContinuousLinearMap.norm_id_le))
 obtain ⟨hh,hT⟩:= arcW (transX hP) hZ (A:=emptyA T x k A F ∘ B) -- tune
 refine ⟨hZ,hh,hT,fun w hw=> ?_,fun w hw=>?_⟩
 · rw [Function.comp_apply, show Vmove x V 0=V from by simp [Vmove]]; have hh:=(edge_gapM (A:=R) (x:=0) hm he hw).unit_det (lt_min he zero_lt_one); rw [hR] at hh; exact hh
 · obtain ⟨ha,hb⟩:= hector (d:=d') (Polar.toBundle hp (room_small hQ)) hm he hC (FreeResolvent.Mark.position_move _ _ hQ.pos.le) hV hQ hv (shipment_near hπ) w hw
   have he:0  ≤  L:=mul_nonneg hQ.vol hQ.meter_abs
   have hp := warp_h (g:=fun U=>perZ T x k A F U w) (front A F) ha hQ.pos he ht
   exact ⟨fuseN hP hp,warp_h (g:=fun U=> tea_r (emptyA T x k A F U) (perZ T x k A F U) w) (front A F) hb hQ.pos (mul_nonneg (Real.exp_pos _).le (Differential.tag_poss le_rfl hQ.m he n)) ht⟩
end
end YM.CF.Neige
