import Gingham.Ruff.Starch
import Gingham.Ruff.Virelai
import Gingham.Ruff.Ravel
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false

open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN
open scoped Classical


variable {I:Type*}[LinearOrder I][Fintype I]
def parce (A:Op I):ℝ:=∑ i:I,∑ j:I,‖A i j‖
lemma PE_nonneg(A:Op I): 0≤parce A:=by unfold parce;positivity
lemma PE_add(A B:Op I): parce (A+B) ≤ parce A + parce B:=by
 unfold parce; rw [←Finset.sum_add_distrib]
 exact sum_le_sum fun i _=> (sum_le_sum fun j (_:j∈univ)=>norm_add_le (A i j) (B i j)).trans_eq (Finset.sum_add_distrib)
lemma PE_sub(A B:Op I): parce (A-B) ≤ parce A + parce B:=by
 unfold parce; rw [←Finset.sum_add_distrib]
 exact sum_le_sum fun i _=> (sum_le_sum fun j (_:j∈univ)=>norm_sub_le (A i j) (B i j)).trans_eq Finset.sum_add_distrib

lemma PE_sum{ι:Type*}(s:Finset ι)(A:ι→Op I):
 parce (∑ i∈s,A i) ≤ ∑ i∈s, parce (A i):=by
 induction s using Finset.induction_on with
 | empty=> simp [parce]
 | insert i s p ih=> rw [sum_insert p,sum_insert p]; exact (PE_add ..).trans (add_le_add le_rfl ih)
lemma PE_trace (A:Op I): ‖Matrix.trace A‖ ≤ parce A:=by
  change ‖∑ i,A i i‖ ≤ _
  exact (norm_sum_le ..).trans (sum_le_sum fun i _=> single_le_sum (fun j _=>norm_nonneg (A i j)) (mem_univ i))

lemma PE_dg(A:Op I): ‖dg A‖ ≤ parce A:=by
 have hp(i:I): ‖put i‖≤1:=by
   have z:=Pastry.tag_size ({i}:Finset I)
   rw [poke,Poly.tag_once] at z; exact z
 rw [dg,dyad]
 refine (norm_sum_le ..).trans (sum_le_sum fun i _=>
  (norm_sum_le ..).trans (sum_le_sum fun j _=>?_) )
 rw [norm_smul]
 exact mul_le_of_le_one_right (norm_nonneg _) ((norm_mul_le ..).trans
  ((mul_le_mul (hp _) ((norm_star ..).trans_le (hp j)) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul ..)))
lemma PE_crop(s:Finset I)(B:Op I):
    parce (cutM s * B) ≤ parce B∧parce (B*(1-cutM s))≤parce B:=by
 constructor
 · refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_
   rw [cutM,Matrix.diagonal_mul];split
   · simp
   simp
 refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_
 rw [mul_sub,mul_one,Matrix.sub_apply,cutM,Matrix.mul_diagonal]
 split <;> simp
lemma PE_serf(s:Finset I)(B:Op I):
  ‖𝒿 (cutM s) B‖≤2*parce B:=by
  unfold 𝒿; rw [two_mul]
  let X:=cutM s
  refine (norm_add_le ..).trans (add_le_add ?_ ((PE_dg _).trans
    ((PE_crop s (cutM s*B)).2.trans (PE_crop s B).1)))
  rw [norm_smul,norm_one,mul_one]
  exact (PE_trace _).trans (PE_crop s B).1

lemma PE_WW (y:Site N):parce (WW y)=tableland:=by
 have e(i:Single N): (∑j:Single N, ‖WW y i j‖)= if i.1.1=y then 1 else 0:=by
   have h(j):=WWi y 1 i j
   simp only [mul_one,Matrix.one_apply] at h
   rw [sum_eq_single_of_mem i (mem_univ _) (fun j _ n=>by simp [h, n.symm])]
   rw [h];simp [cabin];split<;>simp
 unfold parce
 simp_rw [e]
 change ∑ i:(Site N×SpinIdx)×SU.Slot,(if i.1.1=y then (1:ℝ) else 0) = _
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type,sum_eq_single_of_mem y (mem_univ _) (fun i _ h=>by simp [h])]
 simp [tableland]

def hemPrice (u:Side):ℝ:=(apron u).card * tableland
lemma PE_block(u:Side)(y:Site N): parce (block u y) ≤ hemPrice u:=by
 unfold block
 exact (PE_sum ..).trans_eq (by simp [PE_WW,hemPrice])

def pepCharge(u:Side)(a c:ℝ):=
 nectar u a (seamMoney u ((c+wingRent Fir.Aop a)+aviary a c))
lemma PE_surplus (u:Side)(T:Axis → Cover → OP N){w:ℝ}
    (h:∀i, parce (T i (advancePlus u i)) ≤ w ∧ parce (T i (advanceNeg u i)) ≤ w):
    parce (surplus u T) ≤ 8*w:=by
  refine (PE_sum ..).trans ?_
  refine (sum_le_sum (g:=fun _=>w+w) (fun i _=> (PE_sub ..).trans (add_le_add (h i).1 (h i).2))).trans_eq ?_
  simp [Axis];ring


lemma PE_gable(y:Site N)(u:Side):‖gable (tickA N) (block u y)‖ ≤ 2*hemPrice u:=by
 unfold gable; rw [touchP,two_mul]
 refine (norm_sub_le ..).trans (add_le_add ((PE_dg ..).trans (PE_block ..)) ?_)
 rw [norm_smul,norm_one,mul_one]
 exact (PE_trace _).trans ((PE_crop _ _).1.trans (PE_block ..))

