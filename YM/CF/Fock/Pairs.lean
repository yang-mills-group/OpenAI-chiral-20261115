import YM.CF.Fock.Rows

/-!
# Pair polynomial and kinematical identities
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Finset
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]
def squareP (C : Op n) : FC n := ∑ i, ∑ j, C i j • (put i * put j)
def coupl (C : Op n) : FC n := (2:ℂ)⁻¹ • squareP C
def pairTerm (C : Op n) (k : ℕ) : Wave n := ((k.factorial:ℂ)⁻¹) • acts (coupl C ^ k) (vacuum n)
def pairWave (C : Op n) : Wave n := ∑ k∈ range (Fintype.card n+1), pairTerm C k
@[fun_prop] lemma square_cont : Continuous (squareP (n:=n)) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem i j).smul continuous_const
@[fun_prop] lemma coupl_cont : Continuous (coupl (n:=n)) := by
  unfold coupl; fun_prop (disch := apply square_cont)
lemma term_cont (k : ℕ) : Continuous (fun C : Op n => pairTerm C k) :=
  by unfold pairTerm; fun_prop
@[fun_prop] lemma pairWave_cont : Continuous (pairWave (n:=n)) := continuous_finsetSum _ fun i _ => term_cont _
lemma two_put (A : Op n) (i j : n) : quant A*(put i*put j)=
    (create (acts A (basisKet i))*create (acts A (basisKet j)))*quant A := by
  rw [← mul_assoc,quant_put,mul_assoc,quant_put,mul_assoc]
lemma coupl_cov (A C : Op n) : quant A*coupl C=coupl (A*C*Aᵀ)*quant A := by
  unfold coupl; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; congr 1
  unfold squareP; simp_rw [mul_sum,sum_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,two_put]
  simp_rw [create_def,basis_act,sum_mul,mul_sum,sum_mul]
  simp_rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc, Matrix.mul_apply,sum_mul,sum_smul,smul_sum,
    smul_smul, Matrix.transpose_apply]
  -- order
  let D (p q i j : n) := (C i j*(A q j*A p i)) • (put p*put q*quant A)
  change ∑ i,∑ j,∑ p,∑ q, D p q i j=_
  simp_rw [sum_comm (f:=fun i j => ∑ p, ∑ q, D p q i j),
    sum_comm (f:=fun i p => ∑ q, D p q i _),
    sum_comm (f:=fun j p => ∑ i, ∑ q, D p q i j),
    sum_comm (f:=fun i q => D _ q i _),
    sum_comm (f:=fun j q => ∑ i, D _ q i j)]
  simp [D,mul_comm,mul_assoc,mul_left_comm]
lemma pair_cov (A C : Op n) : acts (quant A) (pairWave C)=pairWave (A*C*Aᵀ) := by
  have g : SemiconjBy (quant A) (coupl C) (coupl (A*C*Aᵀ)) := coupl_cov A C
  unfold pairWave; rw [map_sum]; refine sum_congr rfl ?_; intro k _; unfold pairTerm
  rw [map_smul,←act_mul,(g.pow_right k).eq,act_mul,quant_vac]
lemma Degree.couplD {j : ℕ} {x : Wave n} (h : Degree j x) (C : Op n) : Degree (j+2) (acts (coupl C) x) := by
  unfold coupl squareP; rw [act_smul,act_sum]; apply Degree.scale; apply Degree.sumD
  intro i _; rw [act_sum]; apply Degree.sumD; intro i' _; rw [act_smul,act_mul]; exact ((h.putD _).putD _).scale _
lemma pow_degree (C : Op n) (k : ℕ) : Degree (k*2) (acts (coupl C ^ k) (vacuum n)) := by
  induction k with
  | zero => rw [pow_zero,act_one,zero_mul]; exact basis_degree ∅
  | succ k ih => rw [add_mul,one_mul,pow_succ', act_mul]; exact ih.couplD _
lemma term_degree (C : Op n) (k : ℕ) : Degree (k*2) (pairTerm C k) := (pow_degree C k).scale _
@[simp] lemma pairTerm_zero (C : Op n) : pairTerm C 0=vacuum n := by simp [pairTerm]
lemma paired_vac (C : Op n) : (pairWave C).ofLp ∅=1 := by
  rw [pairWave,WithLp.ofLp_sum,Finset.sum_apply,sum_eq_single 0]; simp [vacuum,basisKet]
  · intro k _ h; exact term_degree _ _ _ (by simp only [card_empty]; omega)
  simp

def coupleRow (C : Op n) (i : n) := ∑ j, C i j • put j
lemma Degree.rowD {j : ℕ} {x : Wave n} (h : Degree j x) (C : Op n) (i : n) : Degree (j+1) (acts (coupleRow C i) x) := by
  unfold coupleRow; rw [act_sum]; apply Degree.sumD; intro k _; rw [act_smul]; exact (h.putD _).scale _
lemma put_even (x y z : n) : put x*(put y*put z)=put y*put z*put x := by
  rw [← mul_assoc,show put x*put y= -(put y*put x) from eq_neg_of_add_eq_zero_left (put_put ..),neg_mul,mul_assoc,
    show put x*put z= -(put z*put x) from eq_neg_of_add_eq_zero_left (put_put ..),mul_assoc,mul_neg,neg_neg]
lemma put_coupl (i : n) (C : Op n) : put i * coupl C=coupl C * put i := by
  unfold coupl squareP; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  simp_rw [sum_mul,mul_sum,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,put_even]
lemma row_comm (i : n) (C : Op n) : coupl C*coupleRow C i=coupleRow C i*coupl C := by
  unfold coupleRow; simp_rw [mul_sum,sum_mul,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,put_coupl]
lemma take_even (x y z : n) : takeF x*(put y*put z)-put y*put z*takeF x=
    (if x=y then put z else 0)-(if x=z then put y else 0) := by
  rw [← mul_assoc,show takeF x * put y= _ from eq_sub_of_add_eq (mixed x y), sub_mul,mul_assoc (put y) (takeF x),
    show takeF x * put z= _ from eq_sub_of_add_eq (mixed x z),mul_sub,mul_assoc]
  split <;> split <;> simp [*] <;> abel
lemma pair_pull {C : Op n} (g : Cᵀ= -C) (i : n) : takeF i*coupl C-coupl C*takeF i=coupleRow C i := by
  unfold coupl squareP; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,← smul_sub]
  simp_rw [sum_mul,mul_sum, ← sum_sub_distrib, Algebra.mul_smul_comm,Algebra.smul_mul_assoc, ← smul_sub,take_even]
  have ge (j k : n) : C j k= -C k j := Matrix.ext_iff.mpr g k j
  unfold coupleRow; simp only [smul_sub, smul_ite,smul_zero,sum_sub_distrib]
  rw [sum_comm (f:=fun x y => if i=x then C x y • put y else 0)]; simp only [sum_ite_eq,mem_univ,ite_true]
  simp_rw [ge _ i,neg_smul,sum_neg_distrib, smul_neg,sub_neg_eq_add]
  rw [← add_smul,show (2:ℂ)⁻¹ + 2⁻¹=1 by norm_num,one_smul]
lemma pair_pullPow {C : Op n} (g : Cᵀ= -C) (i : n) (k : ℕ) : takeF i*coupl C^(k+1) =
    (k+1:ℂ) • (coupleRow C i*coupl C^k)+coupl C^(k+1)*takeF i := by
  have he := eq_add_of_sub_eq (pair_pull g i)
  induction k with
  | zero => simp [he]
  | succ k ih =>
    let L := coupleRow C i; let B := coupl C; let a := takeF i
    have g : B*(L*B^k)=L*B^(k+1) := by rw [← mul_assoc,show B*L=L*B from row_comm ..,mul_assoc,pow_succ' B k]
    rw [pow_succ' (coupl C) (k+1),←mul_assoc,he,add_mul,mul_assoc,ih,mul_add, Algebra.mul_smul_comm,g,
      ←mul_assoc (coupl C) (coupl C^(k+1))]
    push_cast; simp [add_smul]; abel
lemma pull_succ {C : Op n} (g : Cᵀ= -C) (i : n) (k : ℕ) : acts (takeF i) (pairTerm C (k+1)) =
    acts (coupleRow C i) (pairTerm C k) := by
  unfold pairTerm; rw [map_smul,←act_mul,pair_pullPow g,act_add,act_smul,
    act_mul (coupl C^(k+1)),show acts (takeF i) (vacuum n)=0 from by rw [←remove_take]; exact vacuum_take _,map_zero,
    add_zero,map_smul,← act_mul,smul_smul]
  congr 1; rw [Nat.factorial_succ]; push_cast
  field_simp
lemma pull {C : Op n} (g : Cᵀ= -C) (i : n) : acts (takeF i) (pairWave C)=acts (coupleRow C i) (pairWave C) := by
  unfold pairWave; rw [map_sum,map_sum,sum_range_succ' (fun k=> acts (takeF i) (pairTerm C k)),
    sum_range_succ (fun k=> acts (coupleRow C i) (pairTerm C k)),pairTerm_zero, ←remove_take, vacuum_take,remove_take]
  rw [((term_degree C (Fintype.card n)).rowD C i).too_big (by omega)]; simp_rw [pull_succ g]
end YM.CF.Fock
