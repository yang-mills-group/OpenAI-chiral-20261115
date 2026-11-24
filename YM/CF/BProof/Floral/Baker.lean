import YM.CF.BProof.Floral.Lace
import YM.CF.Scion.Zest
import YM.CF.Mew.Pot
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll Jet
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
def eat_c : Dough n→ₗ[ℂ] FC n where
 toFun := Subtype.val
 map_add' := fun _ _=>rfl
 map_smul' := fun _ _=>rfl
lemma subhol_dough {D:Set ℂ}{f:D→ Dough n}(p:SubHol D (fun i=>(f i).val)):SubHol D f:=by
 let E:=(eat_c (n:=n)).leftInverse; have he(i:D) : E (f i).val=f i:= LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr Subtype.val_injective : (eat_c (n:=n)).ker=⊥) (f i)
 simpa only [he] using p.linear E -- tune simp ↑
def solve_c {E:Type*}[NormedRing E][NormedAlgebra ℂ E][NormedAlgebra ℝ E][FiniteDimensional ℝ E] {I:Type*}[SemilatticeSup I][OrderBot I][Fintype I][DecidableEq I] : (I→E)→ₗ[ℂ](I→E) where
 toFun:=Scion.reconL.symm
 map_add' := fun _ _=>map_add ..
 map_smul' := fun a x=>Scion.solve _ (a • Scion.reconL.symm x) fun i=> by unfold Stilo.view; change a • x i = _; nth_rw 1 [←Scion.recon x i]; unfold Stilo.view; rw [Finset.smul_sum]; rfl
end YM.CF.Floral
