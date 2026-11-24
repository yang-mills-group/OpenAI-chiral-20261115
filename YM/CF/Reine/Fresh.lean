import YM.CF.Reine.Port
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
local notation "B₀"=>radiusB x
local notation "r₀"=>Stores.till x
local notation "t₀"=>fiery G x S.patch.L
local notation "E₀"=>temp x
open Vol
variable {x'': Config G f}
def clippedP (R:PathData G)(p: BudgetPoint)(r:ℕ)(U:Config G f)(y:Site f):ℝ:= PathData.atomSeries (batch R.cubic r) p U y+PathData.atomSeries (batch R.quartic r) p U y
lemma recoil {o:Support c}(θ:Site f→Site c)(h:∀ u v,separation (θ u) (θ v) ≤ separation u v +10)(i:Site f)(R:PathData G)(p:BudgetPoint)(he:∀ j∈RG.flags p.threshold x'',θ j∈o)(hp:θ i∉halo (v+10) o) : clippedP R p v x'' i=turF R v x'' i:=by
 have hz{m}(P:ℕ→ Atom G m) : PathData.atomSeries (batch P v) p x'' i=gplot (batch P v) x'' i:=by
    refine tsum_congr fun w=> ?_; unfold batch; split
    next z=> exact masked_eq _ _ _ _ (Finset.disjoint_left.mpr (fun j l t=> by have hh:=Push.AbsoluteSums.Paths.where_slot i (P w).leg j ((Push.AbsoluteSums.Paths.atom_foot i (P w)) ▸ l); have hk : separation (θ i) (θ j) ≤ v+10:= (h _ _).trans (Nat.add_le_add_right (hh.trans z) 10); exact (never_c hp (he j t)).not_ge hk)) -- orientation disjoint
    unfold Atom.placed; simp [dimU,RG.masked]
 exact congrArg₂ (·+·) (hz _) (hz _)
lemma bail_f {j: ℕ} {s:Signed}(h:taxM x ≤ j*B₀)(hp:BoltP A U V x)(W:BudgetPoint)(e:W.threshold=t₀)(i:Site f)(u:Sum.inr (Sum.inl i)∈rush x A s j): clippedP T.up W r₀ (pull s 0 U) i= turF T.up r₀ (pull s 0 U) i:=by
 refine recoil S.ratio.parent (fun i j=> ?_) i _ _ (fun i w=>hp.1 s i (by rwa [e] at w)) (fun w=> ((mem_filter.mp u).2 : s.act _ ∉ _ ) ((dome_turn ..).1 (Corona.halo_mono (by unfold taxM at h; omega) (Finset.Subset.refl _) w))) -- tune
 have ht:=Work.E04.parent_separation S.ratio i j; omega
lemma bail_c {j:ℕ} {s:Signed}(h:taxM x ≤ j*B₀)(hp:BoltP A U V x)(W:BudgetPoint)(e:W.threshold=E₀)(i:Site c)(u:Sum.inr (Sum.inr i)∈rush x A s j): clippedP T.down W (Hors.cart x S.patch.L) (pull s 0 V) i=turF T.down (Hors.cart x S.patch.L) (pull s 0 V) i:=by
 have ht:Hors.cart x S.patch.L ≤ r₀:= Nat.div_le_self ..
 refine recoil id (fun i j=> by simp) i _ _ (fun i t=>hp.2 s (by rwa [e] at t)) (fun w=> ((mem_filter.mp u).2 : s.act _ ∉ _) ((dome_turn ..).1 (Corona.halo_mono (by unfold taxM at h; omega) (Finset.Subset.refl _) w)))
end
end YM.CF.Reine
