import YM.CF.Rill.Thane
import YM.CF.Hive.High
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Jet
section both
variable {E F H:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H][NormedSpace ℝ H]
lemma shakeL(f:E→ F)(p:E)(h:Shake f p e l)(L:F→L[ℝ] H):Shake (L ∘ f) p (‖L‖*e) l:=by
 refine ⟨mul_nonneg (norm_nonneg _) h.price, L.contDiff.contDiffAt.comp p h.smooth,fun i u v=> (L.norm_iteratedFDeriv_comp_left (n:=i) h.smooth (Nat.cast_le.mpr v)).trans ?_⟩; exact mul_le_mul_of_nonneg_left (h.bill i u v) (norm_nonneg _)
end both
section fro
open scoped Matrix.Norms.Frobenius
private def sendK: SU.group.Mat →L[ℝ] (SU.F→ SU.F→ℂ):= LinearMap.toContinuousLinearMap (by exact ({toFun:=fun x i j=>x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}:SU.group.Mat →ₗ[ℝ] _)) -- tune top eq
lemma Tender.price_p {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ SU.E){x:E}(h:Tender f x K l):0≤ K:=h.price
private def cutK:=Laic.normL (A:=SU.group.Mat) sendK
private lemma send_p:0 ≤ cutK:=Laic.normZ (A:=SU.group.Mat) _
lemma sentK {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ SU.E){x':E}(h:Tender f x' e l): Shake (fun i x y=>SU.group.mat (f i) x y: E→ SU.F→ SU.F→ℂ) x' (cutK*e) l:=shakeL _ _ h sendK -- tune
end fro
open scoped Matrix.Norms.L2Operator
open Nacre Cube SU Lat
attribute [local instance] opCStarAlgebra
private def dusk:ℝ:=‖(coordL (k:=SU.F)).symm.toContinuousLinearMap‖*cutK
lemma dusk_p:0 ≤ dusk:=mul_nonneg (norm_nonneg _) send_p
lemma purse_f(n:ℕ):∃ b:ℝ,0<b∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ SU.E)(z:E),Tender U z b n→Allows n (SU.fund ∘ U) z 1:=by
 let d:=max dusk 1; have hd:0<d:=lt_of_lt_of_le zero_lt_one (le_max_right ..); refine ⟨1/d,by positivity,fun U i h=>?_⟩
 have hp: Shake (SU.fund ∘ U) i (dusk*(1/d)) n:= by unfold dusk; rw [mul_assoc]; exact shakeL _ _ (sentK _ h) (coordL (k:=SU.F)).symm.toContinuousLinearMap
 refine (hp.paid (CStarRing.norm_of_mem_unitary (show fund (U i) ∈ unitary (Op SU.F) from ?_)).le).mono (max_le ?_ le_rfl)
 · exact SU.fund_U _ -- tune
 rw [one_div,mul_inv_le_iff₀ hd,one_mul]; apply le_max_left
lemma slope(n:ℕ):∃ D:ℝ,1≤ D ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ SU.E)(z:E)(b:ℝ),Tender U z b n→ Shake (fund ∘ U) z (D*b) n:=by
 refine ⟨max 1 dusk,le_max_left ..,fun U z b h=>?_⟩; exact (shakeL _ _ (sentK _ h) (coordL (k:=SU.F)).symm.toContinuousLinearMap).bag (le_trans (le_of_eq (by exact (mul_assoc ..).symm : ‖(coordL (k:=SU.F)).symm.toContinuousLinearMap‖*(cutK*b)=dusk*b)) (mul_le_mul_of_nonneg_right (le_max_right ..) (Tender.price_p U h)))
end YM.CF.Rill
