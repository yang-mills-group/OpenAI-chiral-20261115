import YM.CF.Oise.Ore
import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open ConnectedActivityE6.Art
open Scroll Eire Girt Err Matrix
open Push Push.AbsoluteSums -- tune
open Lich.Muster Vol AnalyticBridge.SectorAffine
variable {N P B C:Side} {m k j:ℕ}{ι:Type}[MeasurableSpace ι]
local notation "G5"=>SU.group
variable {S: StepData N P}{T:Tube SU.group S}{K:Teller SU.group}{F:Forest S.ratio}{A: Stores S}{κ:S.Choices}{q:Chi}{β x C u v σ w e:ℝ}
variable (V:ι→ Config SU.group N)(U:ι→ Config SU.group P)(P₀:Finset (Cell N))(P₁: Finset (Cell P))(W:ι→ Bond N → SU.group.Mat)
section
attribute [local instance] mt
local instance : BorelSpace SU.group.Mat:=⟨rfl⟩
variable (h:Measurable V)(vu:Measurable U)(t:Measurable W)(f:K.Funds S T) (j:ℕ)
private lemma timesH{U V:ι→ SU.group.Mat}(p:Measurable U)(q:Measurable V): Measurable fun i=> U i * V i:=by
 haveI:SecondCountableTopology SU.group.Mat:=by change SecondCountableTopology (Fin SU.group.repDim → Fin SU.group.repDim → ℂ); infer_instance
 exact (show Continuous (fun x:SU.group.Mat × SU.group.Mat=>x.1*x.2) from continuous_fst.mul continuous_snd).measurable.comp (p.prodMk q)
open Offset
variable (Pu Pv:BudgetPoint)(hPu:temp x=Pu.threshold)(hPv:fiery G5 x S.patch.L=Pv.threshold)
include h f vu hPu hPv
lemma sky_a(i:Dill S): Measurable fun j:ι=> Slate.Yaught T (Stores.till x) (fiery G5 x S.patch.L) (temp x) (V j) (U j) κ i:=by
 let Q(i):= wit (V i) (S.prediction (U i) κ); have he:Measurable Q:=by
    have hx: Measurable (fun i=> S.prediction (U i) κ):=(S.prediction_meas (funds_branch f) κ).comp vu
    refine measurable_pi_lambda _ fun i=> SU.group.continuous_mat.measurable.comp (((measurable_pi_apply i).comp h).mul (((measurable_pi_apply i).comp hx).inv))
 obtain ⟨a,b,c,d⟩:=coins_m V U ∅ ∅ Q h vu he f (Stores.till x) Pv Pu; rw [hPu,hPv]; rcases i with i|i|i|i; exact a i; exact b i; exact c i; exact d i
omit hPu hPv h
include f
lemma wall_m(i:Bond N):Measurable (fun x'=>Inure A x q κ v i (U x')):=by
 have hf:Measurable (fun v=>SU.group.mat (S.prediction (U v) κ i)):= SU.group.continuous_mat.measurable.comp ((measurable_pi_apply i).comp ((S.prediction_meas (funds_branch f) κ).comp vu)); unfold Inure; split; exact hf
 exact (shut_m U vu q _).smul hf
lemma flue(i:Site N) :Measurable (fun y=> Esti.litF A x κ (U y) i):=by
 unfold Esti.litF; split; swap; · exact measurable_const
 exact (S.patch.frameMass_meas _).comp (((show Continuous (fun y: Config SU.group P=> expandAt (S.ratio.embed i) y) by unfold expandAt; fun_prop).measurable).comp vu)
lemma drill(i:Bond N): Measurable (fun y=> Esti.litB A x κ (U y) i):=by
 unfold Esti.litB; split; swap; · exact measurable_const
 exact (S.patch.predictorMass_meas _).comp ((S.connector_meas (funds_branch f) κ.1 i).comp vu)
omit f
lemma prism_m(i:Cell P):Measurable (fun x'=> tokenF A q x (U x') i):=by
 have ht(t):Measurable (fun x'=> q.innerShare t (toll (U x') i)):= q.smooth.continuous.measurable.comp ((((tax_m i).measurable.comp vu).div_const _).pow_const (2:ℕ)); unfold tokenF AnalyticBridge.Annulus1AD.profile; split; exact measurable_const.sub (ht _); exact ht _
include h f
lemma tide_m(i:Bond N): Measurable (fun j:ι=> tidal A x w v q (U j) (V j) κ i):= by
 have ht(a:Bool)(V:ι→ℝ)(p:Measurable V)(d:ℝ):Measurable (fun j=> Esti.testing q d (V j) a):=by unfold Esti.testing Esti.cliff; split; exact q.smooth.continuous.measurable.comp (measurable_const.mul p); exact measurable_const.sub (q.smooth.continuous.measurable.comp (measurable_const.mul p))
 refine ht _ _ ((show Continuous (fareG G5) from continuous_const.add (Push.Uniform.traceCharge G5).continuous).measurable.comp ?_) _
 exact timesH (SU.group.continuous_mat.measurable.comp ((measurable_pi_apply i).comp h)) (continuous_star.measurable.comp (wall_m (x:=x) U vu f _))
lemma cupX(K H:Support N): Measurable (fun z=> cohoT A x w v q (V z) (U z) κ K H):=by
 exact ((Finset.measurable_prod _ (fun i _=> prism_m U vu i)).mul (Finset.measurable_prod _ (fun i _=> tide_m V U h vu f i))).mul ((Finset.measurable_prod _ (fun i _=> flue U vu f i)).mul (Finset.measurable_prod _ (fun i _=>drill U vu f i)))
include hPu hPv
lemma case_m(s:Signed)(H:Affine.Window S):Measurable (fun i=>caseP T x A κ q v (U i) (V i) s H):=by
 let Y(x'):Bond N→SU.group.Mat:= Esti.layS q κ A x v (U x') (V x') s; have he:Measurable Y:=by
    apply measurable_pi_lambda; intro i; unfold Y layS; refine timesH (SU.group.continuous_mat.measurable.comp ((measurable_pi_apply i).comp ((Wilson.continuous_pull s 0).measurable.comp h))) (continuous_star.measurable.comp ?_)
    unfold Esti.prism; dsimp only; split; exact continuous_star.measurable.comp (wall_m (x:=x) U vu f _); exact wall_m U vu f _
 let Q:= turnStore s A; obtain ⟨a,b,c,d⟩:=coins_m (pull s 0∘ V) (pull s 0 ∘ U) (traceZ Q.flags) Q.costs Y ((Wilson.continuous_pull ..).measurable.comp h) ((Wilson.continuous_pull ..).measurable.comp vu) he f (Stores.till x) Pv Pu; rw [← hPu,←hPv] at a; rw [← hPu] at b c d -- tune
 exact (((Finset.measurable_sum _ (fun i _=> a i)).add (Finset.measurable_sum _ fun i _=>b i)).add (Finset.measurable_sum _ fun i _=>c i)).add (Finset.measurable_sum _ fun i _=>d i)
end
end YM.CF.Oise
