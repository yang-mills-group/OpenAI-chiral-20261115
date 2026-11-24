import Compass.Energy
import Compass.Schools
import YM.CF.Pec.Sorrel
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
open Complex
local notation "SX"=> SpinIdx
open Spire Pec
abbrev tariffX(s:Signed): Bool:= detX (X s.perm)
lemma taxes (s t:Signed): tariffX (s*t)=(tariffX s).xor (tariffX t):=by rw [tariffX, show X (s*t).perm=X s.perm*X t.perm from rfl,det_p]
lemma tax_i : tariffX 1=false:=det_i
lemma tax_m(i:Axis):tariffX (Signed.mirror i)=false:=det_i
lemma tax_s(i j:Axis)(h:i≠j):tariffX (X (Equiv.swap i j))=true:=detSwap i j h
lemma taxInv(s:Signed):tariffX s⁻¹=tariffX s:=by have h:= taxes s⁻¹ s; rw [inv_mul_cancel,tax_i] at h; cases a:tariffX s⁻¹ <;> cases b:tariffX s<;> first|rfl|(exfalso; rw [a,b] at h; contradiction)
abbrev carriers(N:Side): Subgroup (Sweep N) where
 carrier:= fun i=> Anchored i.s
 one_mem':=Anchored.one
 mul_mem' h t:= Anchored.prod h t
 inv_mem' h:= Anchored.rev h
abbrev taxB {N:Side}(s:Sweep N):Bool:=tariffX s.s
abbrev taxF {N:Side}(s:Sweep N):ℝ:=if taxB s then -1 else 1
lemma tax_prod {N:Side}(s t:Sweep N):taxF (s*t)=taxF s*taxF t:=by unfold taxF taxB; rw [show (s*t).s=s.s*t.s from rfl,taxes]; cases tariffX s.s<;>cases tariffX t.s<;>norm_num
lemma tax_inv {N:Side}(s:Sweep N): taxF s⁻¹=taxF s:=congrArg (fun i:Bool=>if i then (-1:ℝ) else 1) (taxInv s.s)
lemma tax_h(s:Signed)(x:ℂ):(if tariffX s then (-1:ℂ) else 1)*x=hush (tariffX s) x:=by cases tariffX s<;>simp
-- anchors all mirrors, Pec.X rotations pairing
lemma allFlips (s:Signed)(v:s.perm=Equiv.refl _):Anchored s:=by intro i j; rw [v]; rfl
lemma allFlips_perm (s:Signed)(v:∀ i,s.perm i=i):Anchored s:=allFlips _ (Equiv.ext v)
lemma modified (s t:Signed)(v:Anchored t)(p:s.perm=t.perm):Anchored s:=by unfold Anchored at *; rw [p]; exact v
end YM.CF.Compass
