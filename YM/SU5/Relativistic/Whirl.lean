import YM.SU5.Selected.WeldedVac
import YM.SU5.Relativistic.FermiStep
set_option autoImplicit false
set_option synthInstance.maxSize 23000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice
variable (Z:Calibration)(j:Axis){u b:Bool}{F:Family Z}{S:Finset Cover}(z x:ℤ)
variable (p:InTest Z u S b F)
include p
-- grading-blind lifts that fully interoperate: θ mirror includes same phase for all slots
lemma hoops(y:ℤ): chime Z j z (chime Z j y F)=chime Z j (z+y) F:=by
 let T:=mirror Z j 0 F
 rw [←moted Z j (z+y) y z (flow_port Z j y p) (by omega), show chime Z j y F=mirror Z j y T from rfl,reversal Z j y (axial Z j 0 p)]; rfl
lemma counterSlide : chime Z j x (mirror Z j z F) = mirror Z j z (chime Z j (-x) F):=by
 rw [← moted Z j (z+x) z x (axial Z j z p) (by omega),←moted Z j z (z+x) (-x) p (by omega),reversal Z j z p,reversal Z j z (axial Z j (z+x) p)]
lemma faceSlide : chime Z j x (mirror Z j z F) = mirror Z j (z+2*x) (chime Z j x F) := by
  rw [slidesPlane j p z,slidesPlane j (flow_port Z j x p) (z+2*x)]
  have h: mirror Z j 0 (chime Z j x F)=chime Z j (-x) (mirror Z j 0 F):=by rw [counterSlide Z j _ _ p,neg_neg]
  rw [h,hoops Z j _ (axial Z j 0 p),hoops Z j _ (axial Z j 0 p), show z+2*x+-x=x+z by omega]

omit p
lemma signMark {v w:Bool}{F G:Family Z}{u u':Bool}{S T:Finset Cover}(p:InTest Z v S u F)(q:InTest Z w T u' G): F*G= Sector.grainB u u' • (G*F):=funext fun m=>funext fun x=> ((Window.fine_enlarge (subset_univ _) ((p.support m).allV x )).sign_com (Window.fine_enlarge (subset_univ _) ((q.support m).allV x)))
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
