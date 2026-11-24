import GaugeFieldConstruction.Gatoma4
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
namespace Iona
open Rio Grotto Isle Lattice.Corona Ione QuadClock Salt
variable {I:Type}[Fintype I][LinearOrder I]{n: Side}
variable (R:Sweep n)(F F':XE I (InkD n) n) (K K':KK I (Copy n) n)(σ σ':I→Seat n)(μ μ':I→ℝ)(s s':I→ List I)(G G':I→ Hub n)(P Q:List I)
noncomputable def orbit4 : Equiv.Perm (Hub n):=Equiv.ofBijective (moveHub R) ⟨Haro.pure_s R,Finite.surjective_of_injective (Haro.pure_s R)⟩
noncomputable def arm4 : Equiv.Perm (Force n):=Equiv.ofBijective (moveForce R) ⟨flag_b R,Finite.surjective_of_injective (flag_b R)⟩
lemma stamp4 : Same4 (boxA R).symm (orbit4 R) (arm4 R):=by
 refine ⟨fun i=>rfl,fun i=> ?_,fun i=>rfl,fun i=> ?_⟩
 · change Finset.map _ _ = _; rw [Finset.map_eq_image]; rfl
 change Finset.map _ _ = _; rw[Finset.map_eq_image]; rfl
local notation "Zρ"=> ProgramL σ F K μ s G P
local notation "Zt"=> ProgramL σ' F' K' μ' s' G' Q
local notation "O"=> suit_Y R
variable (T i':Finset I) (i:I)(p:i∈P)(l:i∈Q)(h:P.Nodup)(h':Q.Nodup)(t:μ i=μ' i)(v:s i=s' i)(u:G' i=moveHub R (G i))
variable (x:∀ j∈P,j∉s i)(y:∀ j∈ Q,j∉s i)
local notation "X"=> Cuff4
-- align ANY $i$ (one per pair). Enough to match all labels from pairs
variable (u':∀ S:Finset I,S ⊆ (s i).toFinset→passingR n R (fun j=>F (S,j)) (fun j=>F' (S,j))) (v':∀ S:Finset I,S⊆ (s i).toFinset→passingF n R (fun j=>K (S,j)) (fun j=>K' (S,j)))
include p l h h' t v u x y u' v'
lemma courier4 : passingR n R (fun j=>pureX (ProgramL σ F K μ s G P) ({i},j)) (fun j=> pureX (ProgramL σ' F' K' μ' s' G' Q) ({i},j)) ∧ passingF n R (fun j=>(ProgramL σ F K μ s G P).B ({i},j)) (fun j=>(ProgramL σ' F' K' μ' s' G' Q).B ({i},j)) :=by
 have v₀(A:Orbit n): goInR (orbit4 R) F F' (suit_Y R) A.1 (yellA R A).1 (s i).toFinset:= fun ⟨S,j⟩ h=> u' _ h j _
 constructor
 · intro j A; exact Cuff4 (boxA R).symm (orbit4 R) (arm4 R) (stamp4 R) F F' K K' O σ σ' μ μ' s s' G G' P Q (A,fun _=>(0,1,1)) (yellA R (A,fun _=>(0,1,1))) i p l h h' v t u x y (v₀ (A,fun _=>(0,1,1))) j
 intro j S h₀; exact Half4 (boxA R).symm (orbit4 R) (arm4 R) (stamp4 R) F F' K K' O σ σ' μ μ' s s' G G' P Q S (yellA R S) i p l h h' v t u x y (v₀ S) (fun ⟨T,j⟩ h=>v' _ h _ _ h₀) j
#print axioms courier4
end Iona
end YM.CF.Scree.Ing
end
