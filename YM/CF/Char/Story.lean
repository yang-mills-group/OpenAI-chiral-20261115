import YM.CF.Char.Flotte
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows
open Locations Gauges Channels AnalyticNext.QuarticMatch
variable (T:Tube G S)(A:Stores S)(F:Forest S.ratio)(x:ℝ)(V:Config G c)(k:S.Choices)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))
lemma turned {σ E Λ:ℝ} (s:Signed)(b:Site c) (h:T.up.Bounds T.high σ E Λ)(ht:S.patch.Branches S.kernel G): Flow (calendar x A F s b) (fiber s b V S) (unchanged G S) k (Channels.ticket s b k) T V (pull s b V) q d Y (rollY s b x A F Y):=by
 refine ⟨turn_test _ _ _ _ _ _ _ _ ht h,fun a=>?_⟩ -- tune
 dsimp only [calendar]; rw [rack_actual, rack_actual,lift_turn,Joint.main_pull]; congrm _+ ?_
 unfold noiseTaylor; rw [S.prediction_channel ht]; unfold Channels.ticket; rw [show _=k from (S.withinChoice s b).apply_symm_apply k]; exact Joint.energy_channel ..
-- grainA.Bounds not claimed; masks can affect all-history Frame. use termwise
lemma short_h {σ E Λ:ℝ} (h:T.up.Bounds T.high σ E Λ)(U: Config G f)(z:Site f→ G.El):
 mainTerm T.high (grainA T.up r) (gauge z U)=mainTerm T.high (grainA T.up r) U:=by
 let B:=grainA T.up r
 have he (U:Config G f)(z:Site f→G.El)(i: Cell f): B.ell (gauge z U) i=G.adjoint (z i.1) (B.ell U i):=by
    simp only [PathData.ell, PathData.ellTerms, Work.F05.slot_gauge]; rw [← turn_sum]; exact tsum_congr fun j=>(map_smul (G.adjoint _) _ _).symm
 have hx(U:Config G f)(z:Site f→G.El): quadratic T.high B (gauge z U)=quadratic T.high B U:=by simp only [quadratic,face_gauge, G.price_conj, he,G.norm_adjoint]
 have hm{k:ℕ}(A:Atom G k)(h:A.Invariant): (if A.length ≤ r then A else dimA A).Invariant:=by
    split; exact h; intro i j; simp [dimA,Atom.poly]
 unfold mainTerm; change _=Patch.average fun s: Signed=> quadratic T.high B (pull s 0 U)+uncut B.cubic _ + uncut B.quartic _; -- tune
 apply congr_arg; funext s; rw [Work.F05.pull_gauge_zero,hx,Work.F05.uncut_gauge B.cubic (fun i=>hm _ (h.invariant i).2.1),Work.F05.uncut_gauge B.quartic (fun i=>hm _ (h.invariant i).2.2)]
lemma gaugeH {σ E Λ:ℝ}(z:Site c→ G.El)(h:T.up.Bounds T.high σ E Λ)(ht:S.patch.Branches S.kernel G): Flow (room x A F) (rotating (constantGauge z S.ratio)) (outRotation z) k k T V (Lattice.gauge z V) q d Y (gaugeY z x A F Y):=by
 refine ⟨gauge_test _ _ _ _ _ _ _ ht h,fun a=>?_⟩
 dsimp only [PhysicalNext.OrderedAffine2B.SymRows.room]; rw [rack_actual, rack_actual, ← copied S.ratio S.patch.odd_side, rotates,Motion.swing_increment,short_h T h]
 unfold noiseTaylor; rw [(choice_gauge ht _ k _).2, show constantGauge z S.ratio ∘ S.ratio.embed=z from funext fun i=> congr_arg z (S.ratio.embed_parent _)]
 congr 2; apply Finset.sum_congr rfl; intro i _; unfold Lattice.gauge; rw [show z _*V i*_*(z _*_*_)⁻¹= z i.1 * (V i* (S.prediction (increment (replica S.ratio V) a) k i)⁻¹) * (z i.1)⁻¹ by group, G.price_conj] -- tune
end YM.CF.Char
