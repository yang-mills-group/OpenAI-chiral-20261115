import YM.CF.Continuum.CanYo
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Projection
/-!
# Scalar readout linearity on envelope (torus with city-weights)
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Finset Lattice Wilson SU Fock Lat Cube Scree Mir Mir.Trip RP Spire Scroll Tulip Reed Tenant Skye Dial MeasureTheory RG Push.GridApprox
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}(Y:Orbit N→Phys N)
open BoxGauge
open Scree
private lemma cheap (H:Integrable Y (city _))(r:ℕ)(A:paper SU.group r) : Integrable (fun i:Orbit N=> beamL _ (Y i)* BoxGauge.paint r _ A i.1) (city N):=by
 have u:= paid r A
 have he:Envelope (fun i:Orbit N=>BoxGauge.paint r _ A i.1):= u.1.comp_env (((tab_cont ..).measurable).comp measurable_fst); exact ((beamL _).integrable_comp H).mul_bdd he.meas.aestronglyMeasurable (Filter.Eventually.of_forall he.cost.choose_spec)
lemma chips (H:Integrable Y (city _))(r:ℕ)(A B:paper SU.group r) :
    moment Y (bosonic N (BoxGauge.paint r _ (A+B)))= moment Y (bosonic N (BoxGauge.paint r _ A))+moment Y (bosonic N (BoxGauge.paint r _ B)) := by
 simp_rw [boseMoment,BoxGauge.paint,comp_apply,Subalgebra.coe_add,Pi.add_apply,mul_add]; exact integral_add (cheap Y H r A) (cheap Y H r B)
lemma chips_scale (r:ℕ)(A:paper SU.group r)(z:ℂ) : moment Y (bosonic N (BoxGauge.paint r _ (z • A))) = z*moment Y (bosonic N (BoxGauge.paint r _ A)) := by simp_rw [boseMoment,BoxGauge.paint,comp_apply,Subalgebra.coe_smul,Pi.smul_apply,Algebra.mul_smul_comm]; exact integral_smul ..
end YM.CF.Window
