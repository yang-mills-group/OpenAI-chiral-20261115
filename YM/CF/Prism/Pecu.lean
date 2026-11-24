import YM.CF.Prism.Pop
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Prism
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n l:ℕ}{K C Q R v ε d r η t x:ℝ}{c f: Side}{L:Side}
local notation "G"=> SU.group
open Cube (More)
open Tree
variable {S: StepData (More c) (More f)}{F:Forest S.ratio}{T:Tube G S}{V:Pane c}{k:S.Choices}
open CF.Jet
variable (B:BudgetPoint)(o:Seat c) {E D:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup D][NormedSpace ℝ D]{A:tangD c→E}{P:tangD c→D}
def trunk : tangD c→L[ℝ] tangD c:= ContinuousLinearMap.pi fun i=> Lyre.width B o i • (ContinuousLinearMap.proj i)
def silo : tangD c→L[ℝ] tangD c:= ContinuousLinearMap.pi fun i=> (Lyre.width B o i)⁻¹ • (ContinuousLinearMap.proj i)
variable {B o}
lemma trench(u:tangD c): trunk B o (silo B o u)=u :=funext fun i=>smul_inv_smul₀ (Lyre.width_pos ..).ne' _
lemma skin (p: Signs B o A v): Allows B.order (A ∘ trunk B o) 0 v :=by
 let L:=trunk B o
 have hp:ContDiffAt ℝ (B.order:ℕ∞) A (L 0):= (map_zero L).symm ▸ p.paid
 refine ⟨hp.comp _ L.contDiff.contDiffAt,fun j l=>ContinuousMultilinearMap.opNorm_le_bound p.grade fun i=> ?_⟩
 rw [jets_linear (trunk B o) (p.paid.of_le (Nat.cast_le.mpr l)),ContinuousMultilinearMap.compContinuousLinearMap_apply]; refine (seals p _ (fun z=> ‖i z‖) l fun z=> ?_).trans_eq (mul_comm ..) -- tune
 refine ⟨norm_nonneg _,fun e=> ?_⟩; change ‖(Lyre.width B o e) • ((i z e):SU.group.Color)‖ ≤ _; rw [norm_smul, Real.norm_of_nonneg (Lyre.width_pos ..).le, mul_comm]; exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ..) (Lyre.width_pos ..).le
lemma skills (p:Allows B.order (A ∘ trunk B o) 0 v): Signs B o A v:=by
 let L:=silo B o; let F:= A ∘ trunk B o; have hp: ContDiffAt ℝ (B.order:ℕ∞) F (L 0):= (map_zero L).symm ▸ p.smooth
 rw [show A=F ∘ L from funext fun i=> congrArg A (trench i).symm]; refine ⟨p.nonneg,hp.comp _ L.contDiff.contDiffAt,fun i j k v'=>?_⟩
 rw [jets_linear L (p.smooth.of_le (Nat.cast_le.mpr j)),ContinuousMultilinearMap.compContinuousLinearMap_apply]; apply ((iteratedFDeriv ℝ i F 0).le_opNorm _).trans; refine (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun j _=>?_))).trans (p.norm_le _ j)
 refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> ?_; change ‖(Lyre.width B o i)⁻¹ • (k j i)‖ ≤_; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (Lyre.width_pos ..)).le, inv_mul_le_iff₀ (Lyre.width_pos ..),mul_one]; exact v' j i
lemma high (p:Signs B o A v)(l:v ≤ ε):Signs B o A ε:=skills ((skin p).mono l)
lemma mint (p:Signs B o A v){p':tangD c→E}(q:A=ᶠ[𝓝 0] p'):Signs B o p' v:=skills ((skin p).germ (q.comp_tendsto (show Tendsto (trunk B o) (𝓝 0) (𝓝 0) from by simpa using (trunk B o).continuous.tendsto 0)))
lemma hail {y:E}(p:‖y‖≤ v): Signs B o (fun _:tangD c=> y) v:=skills (allows_const _ p) -- tune
lemma haloI {I:Type}{F:I→tangD c→E}{S:Finset I}{f:I→ℝ}(h:∀ i∈S, Signs B o (F i) (f i)): Signs B o (fun x=>∑ i∈S,F i x) (∑ i∈S,f i):=skills (allows_sum fun i p=> skin (h i p))
lemma tack (p: Signs B o A v){A':tangD c→E}(q:Signs B o A' ε):Signs B o (fun w=> A w + A' w) (v+ε):=skills ((skin p).add (skin q))
def pepper (n:ℕ):= (2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℂ‖
lemma patch {y z: tangD c→ℂ}(p: Signs B o y v)(q: Signs B o z ε): Signs B o (fun w=> y w*z w) (pepper B.order*v*ε) :=skills ((skin p).bilinear (ContinuousLinearMap.mul ℝ ℂ) (skin q) le_rfl)
lemma pepperL(n:ℕ):0 ≤ pepper n:=by unfold pepper; positivity
end YM.CF.Prism
