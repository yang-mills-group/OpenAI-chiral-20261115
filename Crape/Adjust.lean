import Crape.Sewn
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Py.Dyad Keeping
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]
-- pure linear algebra absorb relative margin via swept posing.
lemma bill_rel {x x':X}{a a' h f g B:ℝ}(h₀:0<a')(Q:‖(((h*a':ℝ):ℂ))•x'-x‖ ≤ B)(ht:‖((a/a':ℝ):ℂ)‖≤2)(hg:|f|≤g)(e:0≤B) :
 ‖((f*(h*a):ℝ):ℂ) • x'- (f:ℂ) • x‖ ≤ 2*g*B + ‖((a/a'-1:ℝ):ℂ)‖* ‖(f:ℂ) • x‖:=by
 let z:X:=(f:ℂ) • x
 let v:X:=(f:ℂ) • ((((h*a':ℝ):ℂ))•x'-x); have hp:‖v‖ ≤g*B:=by rw [show ‖v‖=|f| *‖(((h*a':ℝ):ℂ))•x'-x‖ from (by unfold v; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs])]; exact mul_le_mul hg Q (norm_nonneg _) ((abs_nonneg _).trans hg)
 rw [show ((f*(h*a):ℝ):ℂ) • x'- (f:ℂ) • x = ((a/a':ℝ):ℂ) • v + ((a/a'-1:ℝ):ℂ) • z from ?_]
 · apply (norm_add_le ..).trans; rw [norm_smul ((a/a':ℝ):ℂ) v,norm_smul ((a/a'-1:ℝ):ℂ) z]; rw [mul_assoc]; exact add_le_add (mul_le_mul ht hp (norm_nonneg _) (by norm_num)) le_rfl
 unfold v z; rw [smul_sub,smul_sub,←mul_smul, ←mul_smul, ←mul_smul]
 rw [show ((a/a':ℝ):ℂ)*(f:ℂ)*(↑(h*a'):ℂ)=(↑(f*(h*a)):ℂ) from (by push_cast; field_simp [h₀.ne']),Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul,mul_smul]
 abel
#check mul_smul
#print axioms bill_rel
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
