import Crape.Balcony
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
variable (P:Spine)(F:ℕ)
local notation "Lx"=>P.par.R.L.val
local notation "K"=>P.calibration
local notation "rC"=>ruler P.par.block
local notation "T"=>timeMesh P.par
abbrev measured (P:Spine)(j:ℕ)(x:ℤ):ℝ := (x:ℝ)/(ruler P.par.block:ℤ)*(mill (timeMesh P.par) j:ℝ≥0)
lemma marks_rec (k:ℤ) (s j:ℕ) (u:j≤ s): measured P s ((Lx:ℤ)^(s-j)*k)=measured P j k:=by
 rw [show measured P s _= (bell T s (castor T j s k))/(rC:ℤ) from (by change measured P s (castor T j s k)=_; unfold measured bell; change ((castor T j s k:ℤ):ℝ)/((rC:ℤ):ℝ)*(mill T s:ℝ)=((castor T j s k:ℤ):ℝ)*(mill T s:ℝ)/((rC:ℤ):ℝ); ring
 ), refineZ _ _ _ u]; unfold measured bell; change (k:ℝ)*(mill T j:ℝ)/((rC:ℤ):ℝ)=(k:ℝ)/((rC:ℤ):ℝ)*(mill T j:ℝ); ring
abbrev tidal (P:Spine)(F j:ℕ):ℝ:= measured P j (nodeC (cellar P F j) (3:Axis))
lemma tide_price(j:ℕ):0<tidal P F j:=by
 unfold tidal measured; have e:= fresh P F j; have he:0<(nodeC (cellar P F j) 3:ℝ):= by exact_mod_cast (show 0<nodeC (cellar P F j) 3 by omega)
 have hm:0<(mill T j:ℝ):=mill_pos _ _ 
 have ht':0<((rC:ℤ):ℝ):=Int.cast_pos.mpr (ruler_gene _); positivity
lemma origin_time (s:ℕ)(w:F ≤ s): measured P s (nodeC (subject P F s) (3:Axis))=measured P F 1:=by
 unfold subject; rw [dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul,Nat.cast_pow]; exact marks_rec P _ s F w -- nodeC 0 maybe not definitional simp cast
lemma adj_time (j:ℕ)(q:F ≤ j): tidal P F j=measured P F 1 + bell T j (setback P F j):=by
 unfold tidal; rw [cellar,bellV,if_pos rfl,←origin_time P F j q]; change measured P j (nodeC (subject P F j) 3+(rC)*setback P F j) = _; unfold measured bell; change (((nodeC (subject P F j) 3+(rC)*setback P F j:ℤ):ℝ)/ _ * (mill T j:ℝ))=_+ (↑(setback P F j):ℝ)*(mill T j:ℝ); rw [Int.cast_add,Int.cast_mul]
 have hp: ((rC:ℤ):ℝ)≠0:= Int.cast_ne_zero.mpr (ruler_gene _).ne'; field
#check crown
#check billX
#print axioms adj_time
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
