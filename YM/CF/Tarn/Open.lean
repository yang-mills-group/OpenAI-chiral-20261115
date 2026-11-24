import YM.CF.Slate.Para
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tarn
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
open AnalyticBridge.RelativeLogdet Ink Next.SectorChange
open Neige FreeResolvent.TestD Souk Slate
variable {D d' V' m:ℝ}{e:Directions G c}{u:E}{f₀:E→Directions G c}
lemma coverZ (hp:Polar (G:=G) (reader G c e) (front (G:=G) (x:=x) A F) (front A F) (baseX T x A F k∘AnalyticBridge.SectorAffine.field V) n d C)(hB: FreeResolvent.Gap (baseX T x A F k (AnalyticBridge.SectorAffine.field V (reader G c e))) m)(hm:0 < m)(hd:0<d)(hc:0≤ C)(h:120≤ radiusB x)
 (hQ:Price d (C+1) (min m 1) d' 1 V' 1 n) (hV:(FreeResolvent.native c).Volume (front (G:=G) A F (x:=x)) d' V') (hR: Allows n f₀ u K)(hu:f₀ u=e) :
 let L:=V'*FreeResolvent.TestD.meter n n (C+1) 1 (rise V' (min m 1)); let U₀:=FreeResolvent.tagPrice 1 n (C+1) L; let ε:=Real.exp (-(n+1:ℕ)*d'*(radiusB x/60:ℕ)); let P:=AnalyticBridge.SectorAffine.field V ∘reader G c ∘ f₀
 let S:=Jet.composeCost n (activation G n 0 d*C) K; let U:=Jet.composeCost n (activation G n 0 d'*L) K
 PriceW (emptyA T x k A F ∘ P) (perZ T x k A F ∘ P) n u (2^n*(S+1)*U) (Jet.composeCost n (activation G n 0 d'*(ε*U₀)) K):=by
 subst e; intro L U₀ ε P X' U'; let f:=AnalyticBridge.SectorAffine.field V; let X:=reader G c ∘ f₀; let Z:=baseX T x A F k; let B:=Z ∘f
 have hπ:=boards A F G h; have hv:=per_self hπ
 have hZ:Ink.Arc (uncurry (perZ T x k A F ∘ P)) n u:=by
    intro t ht; have hp':ContDiffAt ℝ n X u:= (reader G c).contDiff.contDiffAt.comp _ hR.smooth; have hs:= (hp'.comp (f:=Prod.fst) (u,t) contDiffAt_fst).prodMk (show ContDiffAt ℝ n Prod.snd (u,t) from contDiffAt_snd)
    exact (tag_h hv hp hB hm t ht).comp (f:=fun z:E×ℝ=>(X z.1,z.2)) _ hs
 have hK:Protected n (B∘X) u X':= (polar_cash _ _ hp hc hd).comp hR
 have hl:Protected n (emptyA T x k A F ∘ P) u (X'+1):=subsid hK (allows_const u (show ‖paintO (1:Neige.Shelf (Rows.In x A F (G:=G)))‖≤1 by rw [paint_one]; exact ContinuousLinearMap.norm_id_le))
 obtain ⟨hh,hT⟩:= arcW (transX hl) hZ
 refine ⟨hZ,hh,hT,fun w hw=>(edge_gapM (A:=B) (x:=X u) hB hm hw).unit_det (lt_min hm zero_lt_one),fun w hw=>?_⟩
 obtain ⟨ha,hb⟩:= hector (d:=d') (Polar.toBundle hp (room_small hQ)) hB hm hc (FreeResolvent.Mark.position_move _ _ hQ.pos.le) hV hQ hv (shipment_near hπ) w hw
 have he:0  ≤  L:=mul_nonneg hQ.vol hQ.meter_abs
 have hp := (polar_cash _ _ ha he hQ.pos).comp hR
 have hh:= (polar_cash _ _ hb (mul_nonneg (Real.exp_pos _).le (Differential.tag_poss le_rfl hQ.m he n)) hQ.pos).comp hR
 exact ⟨fuseN (n:=n) (B:=fun y=>stepM (panels A F) (emptyA T x k A F (P y)) w) hl hp,hh⟩
end YM.CF.Tarn
