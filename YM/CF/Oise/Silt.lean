import YM.CF.Oise.Yard
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
section
open Scroll Yaw Eire Jet
open Lich.Muster
variable {V Y ι:Type}[MeasurableSpace V][NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup Y][MeasurableSpace Y][NormedSpace ℝ Y] [BorelSpace Y][CompleteSpace Y][SecondCountableTopology Y][MeasurableSpace ι][BorelSpace V][SecondCountableTopology V]
def pace (g:V→ Y)(v a:V):Y:= atTop.limUnder (fun n:ℕ=>(n:ℝ) • (g (a + (n:ℝ)⁻¹ • v)-g a))
variable (T:ι→V→Y)(p b z:ι→V) (h:∀ P:ι→V,Measurable P→ Measurable fun i=> T i (P i))
omit [MeasurableSpace V][BorelSpace V][SecondCountableTopology V][MeasurableSpace Y][BorelSpace Y][SecondCountableTopology Y][CompleteSpace Y] in
lemma pace_eq(g: V→ Y)(a b:V)(h:DifferentiableAt ℝ g b):pace g a b= fderiv ℝ g b a:=by
 have hk : Tendsto (fun n:ℕ=> ‖(n:ℝ)‖) atTop atTop:=by simpa using (tendsto_natCast_atTop_atTop (R:=ℝ)) -- name type
 exact (h.hasFDerivAt.lim a hk).limUnder_eq
include h
lemma pace_m (u:Measurable p)(w:Measurable b): Measurable fun i=>pace (T i) (p i) (b i):=by
 apply StronglyMeasurable.measurable
 unfold pace; refine StronglyMeasurable.limUnder fun n=> ?_; exact (((h _ (w.add (u.const_smul ((n:ℝ)⁻¹)))).sub (h _ w)).const_smul (n:ℝ)).stronglyMeasurable
lemma peak_m (u:Measurable p)(w:Measurable b)(v:Measurable z)(g:∀ i,ContDiffAt ℝ (↑(2:ℕ)) (T i) (p i)): Measurable (fun i=> fderiv ℝ (T i) (p i) (z i)) ∧ Measurable (fun i=> (fderiv ℝ (fderiv ℝ (T i)) (p i)) (b i) (z i)):=by
 let U(i):= Oise.pace (T i) (z i); have he(P:ι→ V)(p:Measurable P):Measurable (fun i=> U i (P i)):= pace_m T z P h v p
 have hz(i): U i =ᶠ[𝓝 (p i)] fun x=> fderiv ℝ (T i) x (z i):=( (g i).eventually (by simp)).mono fun j p=> pace_eq _ _ _ (p.differentiableAt (by norm_num))
 have hv(i): pace (U i) (b i) (p i) = (fderiv ℝ (fderiv ℝ (T i)) (p i)) (b i) (z i):=by
    let A(i):=(ContinuousLinearMap.apply ℝ Y) (z i); have ht:DifferentiableAt ℝ (fderiv ℝ (T i)) (p i):=( (g i).fderiv_right (by norm_num): ContDiffAt ℝ (1:ℕ) (fderiv ℝ (T i)) _).differentiableAt (by norm_num)
    have hf:= ((A i|>.hasFDerivAt).comp (p i) ht.hasFDerivAt).congr_of_eventuallyEq (hz i)
    rw [pace_eq _ _ _ hf.differentiableAt,hf.fderiv]; rfl
 exact ⟨by rw [← funext fun i=> (hz i).self_of_nhds]; exact he p u, ( (congr_arg Measurable (funext hv)).mp (pace_m U b p he w u))⟩
end
end YM.CF.Oise
