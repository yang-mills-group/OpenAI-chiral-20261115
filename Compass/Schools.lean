import YM.CF.Ione.Tick
import YM.Space.Orthogonal
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 25000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
open scoped Classical
-- signed planes P01 fixing.
abbrev classP (i:Axis) :=i∈({0,1}:Finset Axis)
abbrev Anchored (s:Signed):Prop:=∀ i j, (classP (s.perm i)↔classP (s.perm j)) ↔ (classP i↔classP j)
lemma Anchored.one: Anchored 1:=fun _ _=> Iff.rfl
lemma Anchored.prod {s t:Signed}(h:Anchored s)(p:Anchored t): Anchored (s*t):=fun i j=>(h _ _).trans (p i j)
lemma Anchored.rev {s:Signed}(p:Anchored s):Anchored s⁻¹:=fun i j=> (p (s⁻¹.perm i) (s⁻¹.perm j)).symm.trans (by simp)
-- pair table
lemma Anchored.duet {s:Signed}(p:Anchored s):
   (s.perm 0=0 ∧ s.perm 1=1) ∨ (s.perm 0=1 ∧ s.perm 1=0) ∨(s.perm 0=2 ∧ s.perm 1=3)∨(s.perm 0=3 ∧ s.perm 1=2):=by
 have h1 : classP (s.perm 0) ↔ classP (s.perm 1):= (p 0 1).mpr ⟨fun _=> by simp [classP],fun _=>by simp[classP]⟩
 let i:=s.perm 0; let j:=s.perm 1
 have h2:i≠j:=s.perm.injective.ne (by decide:(0:Axis)≠1)
 have hp(i:Axis): i=0∨i=1∨i=2∨i=3:=by fin_cases i <;> decide
 rcases hp i with u|u|u|u <;> rcases hp j with v|v|v|v <;> first| (exfalso; exact h2 (u.trans v.symm))| (rw [show s.perm 0=_ from u,show s.perm 1=_ from v] at h1 ⊢; first|decide|exfalso; apply False.elim; revert h1; decide)
-- analog on Sweep multiplication.S $ later
end YM.CF.Compass
