import YM.CF.Slate.Harp
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=> SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
open Work.E03 AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows
section transform
variable {A A':Stores S}{F F':Forest S.ratio}{P:Box x A A' F F'}{a:ColorOrtho SU.group (Bond f)} {b:ColorOrtho SU.group (Slots S)} {Y:LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{V V':Config SU.group c}{k k': S.Choices}
lemma wheel_p (h:PhysicalNext.OrderedAffine2B.SymRows.Test P a b V V' k k' T q d Y Y')(p:K.Funds S T)(s:Prices SU.group (Active A x F)) (i:Slots S): media i (wheel A' F' T x k' q d Y' (Orthogonal.move (onBond a) P.onKey s) V') = media (P.slots i) (wheel A F T x k q d Y s V):=by
 obtain ⟨v,C,hT,hx⟩:=p.feeds; let u:= Orthogonal.move (onBond a) P.onKey s; have he {A:Stores S}{F:Forest S.ratio}(Y:LinkArray G (Frozen A x F))(k)(s:Prices SU.group (Active A x F))(V:Config SU.group c):wheel A F T x k q d Y s V=selected T x V k (shots S x) A F (fresh x (shots S x) A F (tape s))+ Rows.restrict x (shots S x) A F (Offset.fixedBase T x V k + bump T x V k (Rows.input x A F (autoShell q d V Y))):=by unfold wheel axle; rw [moved _ _ _ _ _ _ _ hT, Offset.f0]; rw [← show ∀ a b:LogArray SU.group (Slots S), tape.symm (a+b)=(tape.symm a)+tape.symm b from fun u v=> Next.SectorChange.colors.symm.map_add u v,tape.apply_symm_apply]
 rw [he,he,funext h.y,frozen_move P.edges a _ P.atH, fresh_move P.edges a _ P.atK]; unfold media selected Rows.restrict; simp_rw [Pi.add_apply, P.begun]; split_ifs
 · simp_rw [h.wave,h.frame]; rw [← map_add (b i),←map_smul (b i),← map_smul (b i),←map_add (b i),← map_smul (b i),(b i).norm_map]
 rfl
end transform
lemma painter_s(h:K.Funds S T)(g:Site c→SU.group.El)(M:Monk G S) (p:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) w)(ht:0<w)(hz:120 ≤ radiusB x)(s: Signed): Slate.payer T x (shiftZ g M) q d l β s= Slate.payer T x M q d l β s:=by
 let Q:=shiftZ g M; obtain ⟨A,B,H,U⟩:=h.feeds; rw [←h.high] at H
 have hb := buzz g M q x β d h l w p ht hz; have hg: Q.sent x T q d l β=Lattice.gauge (constantGauge g S.ratio) (M.sent x T q d l β):= Eq.trans (show Q.sent x T q d l β=landed x M.key M.park (Lattice.gauge g M.V) (gaugeY g x M.key M.park (M.bush x)) (Pogo g M x (M.fuel x T q d l β)) from congrArg (landed x M.key M.park (Lattice.gauge g M.V) (gaugeY g x M.key M.park (M.bush x))) hb) (audU g M x _ _)
 unfold payer; dsimp only; rw [show pull s 0 (shiftZ g M).V=pull s 0 (Lattice.gauge g M.V) from rfl, Work.F05.pull_gauge_zero]; change Yaught T _ _ _ _ (pull s 0 (Q.sent x T q d l β)) _ - _ = _; rw [hg,vega (T:=T) (K:=K) g h]
 refine congrArg₂ (·-·) (rgba _ _ _ (Gauges.turned g s) h _ _) ?_; apply congrArg (Gloss S s); funext i; rw [hb,show liftN T x (Lattice.gauge g M.V) _ _ _ q d _ l=Pogo _ _ _ _ from brag g M q x d h l]
 have hx':= gaugeH T M.key M.park x M.V M.k q d (M.bush x) g H (funds_branch h); exact congrArg₂ (·-·) (wheel_p (P:=room x M.key M.park) hx'.test h (M.fuel x T q d l β) i) (wheel_p hx'.test h _ i) -- tune
end YM.CF.Slate
