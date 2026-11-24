import SatinFixedContrastNovember4
import YM.SU5.Thin.Raze

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
/-!
# Real smearing of the field as an operator

On a fixed Support/RP rectangle (checks that prices apply later),
use smear OP as strong, not norm integral. Export L1, power and convex cost.
-/
open PadThin Sifter
namespace DoseBill
variable (X:Hilbert)(F:SampleDose)(M:ℝ)
variable (A:Vantage→X.Op)(h:∀ x,Continuous (fun i=>A i x))(p: ∀ i,‖A i‖≤M)
def along (F:SampleDose):ℝ:= ∫ v:Vantage, ‖F.val v‖
lemma notNegative : 0 ≤ along F := integral_nonneg fun _=> norm_nonneg _
lemma normalization (f:F.Normalized) : along F=1:= (integral_congr_ae (Eventually.of_forall (fun i:Vantage=> Real.norm_of_nonneg (f.1 i)))).trans f.2
lemma payment (B:ℝ) : Integrable (fun p:Vantage=> ‖F.val p‖*B) := ((F.smooth.continuous.integrable_of_hasCompactSupport F.budget).norm).mul_const _
include h p
private lemma sizeHere (x:X) : ‖(∫ v:Vantage,(F.val v:ℂ) • A v x)‖≤ (along F*M)*‖x‖:=by
  refine (norm_integral_le_integral_norm ..).trans ((integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _)) (payment F (M*‖x‖)) (Eventually.of_forall fun i=>?_)).trans_eq ?_)
  · dsimp only; rw [norm_smul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (p i) (norm_nonneg _))) (norm_nonneg _)
  rw [integral_mul_const, mul_assoc]; rfl
def issue : X.Op := by
  let T: (X)→ₗ[ℂ] X:={
    toFun:=fun x:X=> ∫ v:Vantage,(F.val v:ℂ) • A v x
    map_add':= fun a b=> by
      simp_rw [map_add,smul_add]; exact integral_add (weightedMoney F X _ (h a)) (weightedMoney F X _ (h b))
    map_smul':=fun c a=> by
      simp_rw [map_smul,smul_comm _ c]; exact integral_smul .. }
  exact T.mkContinuous (along F*M) (sizeHere X F M A h p)
-- Lane calculations use this SAME operator at any permitted ℓ.
lemma accomplish (y:X) : issue X F M A h p y=∫ v:Vantage,(F.val v:ℂ) • A v y := rfl
lemma rangeCost : ‖issue X F M A h p‖ ≤ along F*M := (issue X F M A h p).opNorm_le_bound (mul_nonneg (notNegative F) ((norm_nonneg (A 0)).trans (p 0))) (sizeHere X F M A h p)
-- handle all scalar smear addition/smearing mixtures before reading the product
variable (u: Scoop)(v:ℕ→ Vantage→ X.Op)(C:ℕ→ℝ)
variable (u₀:∀ i x, Continuous (fun p=>v i p x))(v₀:∀ i p,‖v i p‖≤ C i)
lemma sumIssue (g:∀ p,A p=u.recipe fun i=>v i p) : issue X F M A h p=u.recipe fun i=> issue X F (C i) (v i) (u₀ i) (v₀ i):= by
  let W(i:ℕ):ℂ:=u.weight i; let V(x:X)(i:Vantage)(j:ℕ):= (F.val i:ℂ) • (v j i x); let I:=u.take
  ext1 x; rw [u.evaluates X,accomplish]; unfold Scoop.recipe; simp_rw [accomplish]
  have he(g':Vantage):(F.val g':ℂ) • (A g' x)= ∑ i∈I,W i • (V x g' i):=by
    rw [g,Scoop.evaluates X,Scoop.recipe,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm _ (W i) _
  simp_rw [he]; rw [integral_finsetSum]; swap; · exact fun i _=> (weightedMoney F X _ (u₀ i x)).smul _ -- `const_smul`
  simp_rw [integral_smul]; rfl
lemma tendContinuum (e':ℝ)(u: ∀ i p,‖v i p‖ ≤ e') (g:∀ x, ∀ y∈ tsupport F.val, Tendsto (fun i:ℕ=> v i y x) atTop (𝓝 (A y x))) (x:X):
    Tendsto (fun i:ℕ=> issue X F (C i) (v i) (u₀ i) (v₀ i) x) atTop (𝓝 (issue X F M A h p x)) := by
  simp_rw [accomplish]
  apply tendsto_integral_of_dominated_convergence (fun p:Vantage=> ‖F.val p‖*(e'*‖x‖))
    (fun i=>(weightedMoney F X _ (u₀ i x)).aestronglyMeasurable) (payment F _) (fun i=>ae_of_all _ fun p=>?_) (ae_of_all _ ?_)
  swap
  · rw [norm_smul, Complex.norm_real]; exact mul_le_mul_of_nonneg_left (((v i p).le_opNorm _).trans (mul_le_mul_of_nonneg_right (u i p) (norm_nonneg _))) (norm_nonneg _)
  intro y; by_cases e:y∈ tsupport F.val
  · exact (g x y e).const_smul _
  rw [image_eq_zero_of_notMem_tsupport e,Complex.ofReal_zero,zero_smul]; simp_rw [zero_smul]; exact tendsto_const_nhds
end DoseBill
open DoseBill
#print axioms DoseBill.tendContinuum
#print axioms DoseBill.sumIssue
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
