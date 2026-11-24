import YM.CF.Continuum.CanYo
import YM.Cells.Interior

/-!
# first cut with the reflected form on donor gauge probes

The scalar form here is still induced by the complex weights of the FiniteGaugeData donor.
The Polar inequality on the gauge Wilson probability would not justify this one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Lat Cube RP Push.GridApprox Topology Skye Scree Fock SU Spire Scroll Tulip
open scoped Classical Topology BigOperators ContDiff InnerProductSpace ComplexOrder ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
namespace SquareScalar
variable {m B:Side}{P:Patch}
local notation "Λ" => CSide m B
lemma unit_price (F:Evaluation Λ→ℂ)(X: Pane Λ→ℂ)(s:Axis)(u: F 1=1)(h:ξTape s P _ X)
    (e:∀ (X:Fin 2→Pane (CSide m B)→ℂ), (∀ i,ξTape s P _ (X i)) → (reflectionForm s F (fun i=>bosonic (CSide m B) (X i))).PosSemidef ):
    ‖F (bosonic (CSide m B) X)‖^2 ≤ ‖F (bosonic (CSide m B) ((θBack s X) * X))‖ := by
 let Z : Fin 2→Pane Λ→ℂ:=![1,X]; have he:= e Z (fun i=> by fin_cases i <;> first | exact h | exact Cells.Interior.constant _ 1)
 let k:= reflectionForm s F (fun i=>bosonic (CSide m B) (Z i)); change k.PosSemidef at he
 have hv := he.det_nonneg; have hg(i j:Fin 2): k i j=F (bosonic Λ ((θBack s (Z i))* (Z j))):= by unfold k reflectionForm crossForm; simp [θ_bosonic,boseP]
 have hu: θBack s (Z 0)=1:= funext fun x=> star_one _
 have hh:bosonic Λ (Z 0)=1:=funext fun x=> one_smul ..
 have hp : k 1 0=star (k 0 1) := by rw [←Matrix.conjTranspose_apply]; exact (congrFun (congrFun he.isHermitian.eq 1) 0).symm
 rw [Matrix.det_fin_two, hp, hg 0 0,hu,one_mul,hh,u,one_mul] at hv
 have hs: (k 0 1* star (k 0 1)).re=‖k 0 1‖^2:= by rw [Complex.star_def,Complex.mul_conj,Complex.ofReal_re]; exact (Complex.sq_norm ..).symm
 have ha: k 0 1= F (bosonic (CSide m B) X):= by rw [hg,hu,one_mul]; rfl
 have hz: ‖k 0 1‖^2≤ ‖k 1 1‖:= by rw [← hs]; exact (sub_nonneg.mp (show _ from (Complex.le_def.mp hv).1)).trans (Complex.re_le_norm _)
 rw [ha,hg 1 1] at hz; exact hz
end SquareScalar
end YM.CF.Window
