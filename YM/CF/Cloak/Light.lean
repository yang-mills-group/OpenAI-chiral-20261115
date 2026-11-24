import YM.CF.Cloak.Yarn
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
section bound
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x₀:E}{U:E→ Config G f}{u v C D:ℝ}{T:E→X}[NormedAddCommGroup X][NormedSpace ℝ X]
local notation "m"=> SU.group.colorScale
lemma shoulder (q:Chi)(D C:ℝ)(n:ℕ)(t:m≤C)(h:∀ x,Allows n (cliff true q) x D)(s:ℝ)(p:0<s)(F:E→SU.group.El)(u:Tender F x₀ (C*s) n):Allows n (fun x=> q.innerShare (s/2) (SU.group.chord (F x))) x₀ (let X:=m⁻¹*C; Jet.composeCost n D (4*(2^n*X*X))) :=by
 let f(x):=F x; let A(x):=4*(SU.group.chord (F x)/s)^2; let X:=m⁻¹*C
 have he:(fun x=>q.innerShare (s/2) (SU.group.chord (F x)))=cliff true q∘ A:=by ext x; unfold cliff Chi.innerShare; simp only [comp_apply,ite_true]; congr 1; unfold A; field_simp; ring
 rw [he]; by_cases g:SU.group.chord (F x₀) ≤ s
 · have hx:Allows n A x₀ (4*(2^n*X*X)):=by simpa using ((white s p F u g t).smul 4); -- tune
   exact (h _).comp hx
 let K:= Jet.composeCost n D (4*(2^n*X*X)); have hh:0 ≤ D:=(h 0).nonneg; have hk:0≤ K:=by have hc:0≤C:=SU.group.colorScale_pos.le.trans t; unfold K Jet.composeCost X; have hg:= SU.group.colorScale_pos; positivity
 have hu:ContinuousAt F x₀ :=(SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr u.smooth.continuousAt
 apply (allows_const x₀ (v:=(0:ℝ)) (by simpa using hk)).germ; filter_upwards [((SU.group.continuous_chord.continuousAt).comp hu).eventually (lt_mem_nhds (lt_of_not_ge g))] with x l; change s<_ at l; refine Eq.symm (q.to_zero _ ?_); have hw:1 ≤ SU.group.chord (F x)/s:=(le_div_iff₀ p).mpr (by rw [one_mul]; exact l.le); unfold A; nlinarith
-- let cutoff support through exact pole hooks : ≤s/2 uses plateau, ≥s kills with derivative exactly.
abbrev pad(F:E→ SU.group.El)(s:ℝ)(x:E):= q.innerShare (s/2) (SU.group.chord (F x)) -- q implicit
lemma pad_eq (q:Chi)(s:ℝ)(h:0<s)(F:E→ SU.group.El)(p:SU.group.chord (F x₀) ≤ s/2):q.innerShare (s/2) (SU.group.chord (F x₀))=1:=q.to_one _ (pow_le_one₀ (div_nonneg (SU.group.chord_nonneg _) (half_pos h).le) ((div_le_one (half_pos h)).mpr p))
lemma shade_s(q:Chi)(s:ℝ)(p:0<s)(F:E→ SU.group.El)(h:Tender F x₀ v n)(ht:x₀∈tsupport (fun x=>q.innerShare (s/2) (SU.group.chord (F x)))) : SU.group.chord (F x₀)≤ s:=by
 have hu:ContinuousAt F x₀ := (SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr h.smooth.continuousAt; by_contra! t
 have hv:= ((SU.group.continuous_chord.continuousAt).comp hu).eventually (lt_mem_nhds t); obtain ⟨a,p',v⟩:= frequently_principal.mp ((mem_closure_iff_clusterPt.mp ht).frequently hv) -- tune
 have hm:= q.chosen_lt (SU.group.chord (F a)) (s/2) (half_pos p) (show _ from p'); change s < SU.group.chord (F a) at v; linarith
end bound
end YM.CF.Cloak
