import SatinThinShaft
import YM.CF.BPress.Spin.Signed
set_option autoImplicit false
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
/- aggregate all costs, keep columns for sales -/
lemma rev_stock (P Q:Op I)(c:ℝ)(h:∀ i:I,(∑ j:I, ‖P j i‖) ≤ c): revE (P*Q) ≤ c*revE Q:=by
 rw [revE_cols (P*Q), revE_cols Q,mul_sum]; apply sum_le_sum; intro i _
 rw [mul_sum]; apply le_trans (b:=∑ j:I,∑ k:I, ‖P j k‖*‖Q k i‖) (sum_le_sum (fun j _=>?_)) ?_ ; swap
 · rw [Matrix.mul_apply]; simp_rw [←norm_mul]; apply norm_sum_le
 rw [sum_comm]; apply sum_le_sum; intro j _; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (h _) (norm_nonneg _)
lemma rev_add (P Q:Op I) : revE (P+Q) ≤ revE P + revE Q:=by
 unfold revE; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [←sum_add_distrib]; exact sum_le_sum fun j _=> norm_add_le ..
lemma rev_star (P:Op I) : revE (star P)=revE P:=by rw [revE_cols (star P)]; simp [Matrix.star_apply,revE]
lemma rev_neg (P:Op I) : revE (-P)=revE P:=by simp [revE]
lemma rev_tunders (P Q:Op I)(C:ℝ)(h:∀ i:I,(∑ j:I, ‖P i j‖)≤ C): revE (Q*P) ≤ C*revE Q:=by
 rw [←rev_star (Q*P),←rev_star Q,star_mul]; apply rev_stock; intro i; simpa [Matrix.star_apply] using h i
lemma rev_smul (c:ℝ)(P:Op I): revE (c•P)=|c| *revE P:=by simp only [revE,mul_sum,norm_smul,Matrix.smul_apply,Real.norm_eq_abs]
lemma rev_storm (α:Type*)[Fintype α](F:α→ Op I)(S:Finset α): revE (∑ j∈ S,F j)≤ ∑ j∈S, revE (F j):=by
 classical
 induction S using Finset.induction_on with
 | empty => simp [revE]
 | @insert i S h ih=> simpa only [sum_insert h] using (rev_add (F i) (∑ i∈ S,F i)).trans (add_le_add_right ih _)
lemma rev_jazz (b:Bool)(P:Op I): revE (Thera.jazz b P)=revE P:=by
 unfold Thera.jazz; split; · rw [rev_neg,rev_star]
 rfl
lemma rev_perm (P:Op I)(A:I≃ I): revE (P.submatrix A A)=revE P:=by
 unfold revE; rw [←Equiv.sum_comp A (fun i=>∑ j,‖P i j‖)]; exact sum_congr rfl fun i _=> Equiv.sum_comp A (fun j=> ‖P (A i) j‖)

open BPress.Spin BPress.Spin.SpinSign Nacre Pledge Sifting Spire
variable (v:Signed) {N:Side}
lemma ω_breeze (j:Single N) : (∑ i:Single N,‖(ω0 v N).val i j‖) ≤ 180:=by
 cases j with
 | mk a s=>
   rcases a with ⟨x,j⟩
   rw [Fintype.sum_prod_type,Fintype.sum_prod_type, sum_eq_single x]
   · refine le_trans (sum_le_sum (g:=fun _=>∑ _i: SU.Slot,(1:ℝ)) (fun i _=>sum_le_sum (fun k _=> (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (ω0 v N).property).le))) ?_; simp only [sum_const,nsmul_eq_mul,card_univ,SpinIdx, Fintype.card_fin, SU.slots]; norm_num -- orientation?
   · intro i _ p; apply sum_eq_zero; intro a _; apply sum_eq_zero; intro l _; refine norm_eq_zero.mpr ?_; change jump (Equiv.refl _) (fun i:Site N =>(milU (incX v) (spinX v) inert i).val) (i,a,l) (x,j,s)=0; rw [jump_apply]; exact if_neg p
   simp
lemma rev_foil (f:Bkg (More N)→Op (Single N)) (x:Bkg (More N)): revE (Nacre.foil v f x) ≤ 180^2*revE (f (Yg (incX v⁻¹) x)):=by
 let A:= names v N; let W:=ω0 v N; let P:=f (Yg (incX v⁻¹) x); rw [Nacre.foil,zone_c]; change revE (jazz (detX v) (twist (prepU (incX v) (spinX v) _ _) _))≤_; rw [SpinSign.bond,twin,twist_formula,π0_twist, rev_jazz];
 apply (rev_tunders (star W.val) _ 180 ?_).trans; swap
 · intro i; simpa [W,Matrix.star_apply] using ω_breeze (N:=N) v i
 let Q:=P.submatrix A A; change 180* revE (W.val*Q)≤ _; refine (mul_le_mul_of_nonneg_left (rev_stock (ω0 v N).val Q 180 (ω_breeze v)) (by norm_num : (0:ℝ)≤180)).trans_eq ?_; rw [show revE Q= _ from rev_perm P A]; change _=_ * revE P; ring -- binder ambiguity
end YM.CF.Papyrus.Franc
#print axioms YM.CF.Papyrus.Franc.rev_foil
