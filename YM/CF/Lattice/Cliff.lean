import YM.CF.Operator.Blocks

/-! Explicit Euclidean spin matrices. Order as in candidate finite statement §e:spin. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF
open Complex
open scoped Matrix

abbrev SpinIdx := Fin 4

-- columns with upper spin followed by lower spin
-- γ1[upper/lower]=-iσ1; γ2=-iσ2; γ3=-iσ3; γ4=I there.
def gammaOp : Fin 4 → Op SpinIdx :=
  ![!![0,0,0,-I;
       0,0,-I,0;
       0,I,0,0;
       I,0,0,0],
    !![0,0,0,-1;
       0,0,1,0;
       0,1,0,0;
       -1,0,0,0],
    !![0,0,-I,0;
       0,0,0,I;
       I,0,0,0;
       0,-I,0,0],
    !![0,0,1,0;
       0,0,0,1;
       1,0,0,0;
       0,1,0,0]]

def grading : Op SpinIdx := !![1,0,0,0;0,1,0,0;0,0,-1,0;0,0,0,-1]

def spinJ : Op SpinIdx := !![0,1,0,0;-1,0,0,0;0,0,0,1;0,0,-1,0]

-- prove by explicit multiplication
lemma gammaAdj (i) : IsSelfAdjoint (gammaOp i) := by
  fin_cases i <;> rw [isSelfAdjoint_iff] <;> ext x y <;> fin_cases x <;> fin_cases y <;> simp [gammaOp]
lemma gammaOne (i) : gammaOp i * gammaOp i = 1 := by
  fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;> norm_num [gammaOp,Matrix.mul_apply,Fin.sum_univ_succ, SpinIdx,Matrix.one_apply]
set_option maxHeartbeats 1600000 in
lemma gammaSwap (i j) (h:i≠j) : gammaOp i * gammaOp j = -(gammaOp j * gammaOp i) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals ext x y; fin_cases x <;> fin_cases y <;> norm_num [gammaOp,Matrix.mul_apply,Fin.sum_univ_succ, SpinIdx]

set_option maxHeartbeats 800000 in
lemma grading_rule : grading = gammaOp 0 * gammaOp 1 * gammaOp 2 * gammaOp 3 := by
  rw [show (3:Fin 4)=Fin.succ (Fin.succ (Fin.succ 0)) from rfl, show (2:Fin 4)=Fin.succ (Fin.succ 0) from rfl]
  ext x y; fin_cases x <;> fin_cases y <;> simp only [Matrix.mul_apply, SpinIdx, Fin.sum_univ_succ, gammaOp, grading, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> norm_num <;> simp only [show (2:Fin 4)=Fin.succ (Fin.succ 0) from rfl, show (2:Fin 3)=Fin.succ (Fin.succ 0) from rfl, Matrix.cons_val_succ, Matrix.cons_val_zero] <;> norm_num
lemma gradingAdj : IsSelfAdjoint grading := by
  rw [isSelfAdjoint_iff]; ext x y <;> fin_cases x <;> fin_cases y <;> simp [grading]
lemma gradingOne : grading * grading = 1 := by
  ext x y <;> fin_cases x <;> fin_cases y <;> norm_num [grading,Matrix.mul_apply,Fin.sum_univ_succ, SpinIdx,Matrix.one_apply]
lemma gradingSwap (i) : grading * gammaOp i = -(gammaOp i * grading) := by
  fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;> norm_num [grading,gammaOp,Matrix.mul_apply, SpinIdx, Fin.sum_univ_succ]
lemma spinJ_star : star spinJ = -spinJ := by
  ext x y <;> fin_cases x <;> fin_cases y <;> simp [spinJ]
lemma spinJ_real : cc spinJ = spinJ := by
  ext x y <;> fin_cases x <;> fin_cases y <;> simp [spinJ]
lemma spinJ_sq : spinJ*spinJ= -1 := by
  ext x y <;> fin_cases x <;> fin_cases y <;> norm_num [spinJ,Matrix.mul_apply,Fin.sum_univ_succ, SpinIdx,Matrix.one_apply]
lemma spinJ_unitary : spinJ ∈ unitary (Op SpinIdx) := by
  constructor <;> simp [spinJ_sq,spinJ_star]
lemma spinJ_inter (i) : gammaOp i * spinJ = spinJ * cc (gammaOp i) := by
  fin_cases i <;> ext x y <;> fin_cases x <;> fin_cases y <;> norm_num [gammaOp,spinJ,Matrix.mul_apply,Fin.sum_univ_succ, SpinIdx]
lemma spinJ_grading : grading * spinJ = spinJ * cc grading := by
  rw [grading_rule]; simp only [cc_mul]
  simp only [mul_assoc, spinJ_inter 3]
  calc
    _ = spinJ * (cc (gammaOp 0) * (cc (gammaOp 1) * (cc (gammaOp 2) * cc (gammaOp 3)))) := by
      rw [← mul_assoc (gammaOp 2), spinJ_inter, mul_assoc spinJ,
        ← mul_assoc (gammaOp 1), spinJ_inter, mul_assoc spinJ,
        ← mul_assoc (gammaOp 0), spinJ_inter, mul_assoc spinJ]
end YM.CF
