import YM.CF.Moto.Rune
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Moto
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Hove Haro
variable {n:Side}(o x y:Site n)(a b:Pal)(S T:Matrix (Single n) Kt ℂ)(P:Op (Single n))(k:ℕ)(g:SU.E)(r:Bool)(i:Axis)
lemma maple(P:Op (Single n))(v:∀ p q:Prism.Rock n,∀ g:SU.E,Commute (boxM P p q) (mater g)): MarkPH P:=by
 intro g u z
 let T:=matPH P u z
 have hm:Commute T (KinX g):=by
    unfold Commute SemiconjBy; ext ⟨x,a⟩ ⟨y,b⟩; rw [Matrix.mul_apply, Matrix.mul_apply]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (fun l:SpinIdx ×Slot=> (KinX _) _ l * T l (y,b))]; rw [sum_eq_single y,sum_eq_single x]
    · simp only [KinX,Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul]; exact Matrix.ext_iff.mpr ((v (u,x) (z,y) g).eq) a b
    · intro i _ h; simp [T,KinX,Matrix.one_apply,h,Ne.symm h]
    · simp
    · intro i _ h; simp [T,KinX,Matrix.one_apply,h,Ne.symm h]
    simp
 exact hm
end YM.CF.Moto
