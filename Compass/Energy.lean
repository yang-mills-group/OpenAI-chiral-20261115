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
structure Moncol (M:Op n): Prop where
 subsingle(i:n):∀ j k,M j i ≠0 → M k i ≠0 → j=k
variable {M:Op n}
-- one-way roof_x.S
lemma roof_g(X Y:Finset n)(p:∀ i j,M i j≠0→ j∈Y → i∈X):cutM X.powerset*quant M*cutM Y.powerset=quant M*cutM Y.powerset:=by rw [←quantCut,←quantCut,←quant_mul,←quant_mul,←quant_mul]; congr 1; ext i j; by_cases v:M i j=0; simp [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal,v]; by_cases u:j∈Y <;> simp_all only [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal, mul_ite,mul_one,mul_zero, ite_true, ite_false]; rw [if_pos (p i j v u),one_mul] -- maybe no goals
open scoped Classical
lemma Monselt (F G:Finset n) (p:∀ i j,M i j≠0→ j∈G → i∈F)(U W:Finset n)(q:quant M U W≠0)(h: W⊆ G):U⊆F:=by
 have ht:= Matrix.ext_iff.mpr (roof_g F G p) U W
 rw [cutM,cutM,Matrix.mul_diagonal, if_pos (mem_powerset.mpr h),mul_one,Matrix.diagonal_mul,Matrix.mul_diagonal,if_pos (mem_powerset.mpr h),mul_one] at ht
 by_contra t; rw [if_neg (mt mem_powerset.mp t),zero_mul] at ht; exact q ht.symm
lemma Moncol.wedges (X:Moncol M): Moncol (quant M):=by
 let m(i:n):n:=dite (∃ j:n,M j i≠0) Classical.choose (fun _=>i); have H(i j:n)(p:M j i≠0): m i=j:=X.subsingle i _ _ (show M (m i) i≠0 from (by unfold m; let t:∃ j:n,M j i≠0:= ⟨j,p⟩; rw [dif_pos t]; exact Classical.choose_spec t)) p
 have he(x y:Finset n)(a:quant M x y≠0): x=y.image m:=by
    apply Finset.eq_of_subset_of_card_le (Monselt _ y (fun i j t q=>mem_image.mpr ⟨j,q,H _ _ t⟩) x y a (Subset.refl _)); have h:y.card=x.card:=(Classical.byContradiction (fun t=> a (quant_grade M x y t)):x.card=y.card).symm; exact h ▸ card_image_le
 constructor; exact fun i j k t w=> (he _ _ t).trans (he _ _ w).symm
end YM.CF.Compass
