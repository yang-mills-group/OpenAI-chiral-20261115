import YM.CF.Vp929.Rails.Field
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP Push.AbsoluteSums Push.AbsoluteSums.Trees RG
open scoped Classical
variable {ι J : Type}[Fintype ι][DecidableEq ι][LinearOrder J][Fintype J] {V:Side} {T:Type}
local notation "Lo"=> leaf (Site V)
local notation "X'"=> Finset ι
local notation "Sc"=> X'→ Lo→Raid J

variable {C: Raid J} {D:ℕ} {q:T→ℝ}{B:T→Finset ι→ℝ}{δ a r:ℝ}{L:ℕ→ℝ} (S:T→ Finset ι→leaf (Site V)→Raid J)
variable (g:∀ i,Merit D (a+δ) C (B i) L (S i))(hp:∀ i,0≤B i)(p:0≤C)[Fintype T]
variable {P:Finset ι→ leaf (Site V)→Raid J} (G:T→Finset ι→ leaf (Site V)→ℝ)(hb:0≤P)(hq:0≤q)(ht:(∑ i,q i)=1)(hr:0≤ r)(u:∀ i x, joinV C (P i x)≤ ∑ j:T,G j i x* joinV C (S j i x))(e:∀ i x y,G i x y≤ q i * (B i x* r)*Trees.currency D δ y.val)
include p G hp hq ht hr g
include hb u e
lemma Merit.take : Merit D a C (fun (_:Finset ι)=>1) (fun i=>r*L i) P:= by
 have t (i:T) (x:X') (y:Lo):0≤ joinV C (S i x y):= sum_nonneg fun j _=> mul_nonneg (p j) ((g i).p x y j); refine ⟨hb,fun x n=>?_⟩
 calc
  _≤∑ i:T,q i*(r*tallY D (a+δ) (B i) C (S i) x n):= by
    unfold tallY; simp_rw [mul_sum,one_mul]; rw [sum_comm (s:=(univ:Finset T))]; apply sum_le_sum; intro i _; rw [sum_comm (s:=(univ:Finset T))]; apply sum_le_sum; intro y _
    apply le_trans (mul_le_mul_of_nonneg_right (u i y) (Real.exp_pos _).le); rw [sum_mul]; apply sum_le_sum; intro j _; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (e j i y) (t j i y)) (Real.exp_pos _).le).trans_eq; unfold Push.AbsoluteSums.Trees.currency; rw [add_mul,Real.exp_add]; unfold joinV; simp_rw [←Finset.mul_sum]
    ring
  _≤∑ i:T,q i*(r*L n):= sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((g i).earn x n) hr) (hq i)
  _= _:= by rw [←sum_mul,ht,one_mul]
end YM.CF.Yaw
