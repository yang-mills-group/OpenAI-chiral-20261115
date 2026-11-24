import Zephyr.Chern.Piola
import YM.CF.Lattice.Cliff
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF Matrix Finset


def Cg : Five → Op SpinIdx :=
  Fin.cases (-grading) (fun i=>Complex.I • (grading * gammaOp i))

@[simp] lemma Cg_0 : Cg 0= -grading := rfl
lemma Cg_pair (i j:Axis) :
    Cg i.succ * Cg j.succ = gammaOp i * gammaOp j := by
  change (Complex.I • (grading * gammaOp i)) * (Complex.I • (grading * gammaOp j))=_
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Complex.I_mul_I,
    gradingSwap i, neg_mul,mul_assoc, ←mul_assoc grading grading,gradingOne,
    one_mul,neg_smul,one_smul,neg_neg]

lemma Cg_square (i:Five) : Cg i * Cg i = 1 := by
  induction i using Fin.cases
  · rw [Cg_0,neg_mul_neg,gradingOne]
  rw [Cg_pair,gammaOne]

private lemma Cg_base (i:Axis) : Cg 0 * Cg i.succ= -(Cg i.succ * Cg 0) := by
  change -grading * (Complex.I • (grading * gammaOp i))= -((Complex.I • (grading * gammaOp i))* -grading)
  rw [Matrix.mul_smul,Matrix.smul_mul,neg_mul,
    ←mul_assoc,gradingOne,one_mul,gradingSwap i, neg_mul,mul_neg,
    mul_assoc,gradingOne]; simp

lemma Cg_swap {i j: Five} (p : i≠j) : Cg i * Cg j = -(Cg j * Cg i) := by
  induction i using Fin.cases

  · induction j using Fin.cases
    · exact (p rfl).elim
    exact Cg_base _
  induction j using Fin.cases
  · rw [Cg_base,neg_neg]
  rw [Cg_pair,Cg_pair,gammaSwap]
  exact fun e=>p (congrArg Fin.succ e)

private lemma Cg_three (i j k : Five) :
    (Cg i * Cg j * Cg k).trace=0 := by
  obtain ⟨h,a,b,c⟩ : ∃ h:Five, h≠i ∧ h≠j ∧ h≠k := by
    by_contra! g
    -- rename Fin.val
    have v:=g (0:Five); have w:=g (1:Five)
    have u:=g (2:Five); have t:=g (3:Five)
    grind
  let Z:= Cg i * Cg j * Cg k
  have e : Cg h * Z = -(Z * Cg h) := by
    unfold Z; rw [←mul_assoc,←mul_assoc,Cg_swap a,
      neg_mul,mul_assoc,Cg_swap b,mul_neg,neg_neg,←mul_assoc,mul_assoc,Cg_swap c]
    simp only [mul_assoc,mul_neg]
  have t:= congrArg (fun U=> (U * Cg h).trace) e
  change ((Cg h*Z)*Cg h).trace = _ at t
  rw [trace_mul_comm, ←mul_assoc, Cg_square, one_mul, neg_mul,mul_assoc,Cg_square,mul_one,trace_neg] at t
  exact (mul_eq_zero.mp ((two_mul _).trans (add_eq_zero_iff_eq_neg.mpr t))).resolve_left two_ne_zero

abbrev Quint := Five → ℂ

def wand : Quint →ₗ[ℂ] Op SpinIdx where
  toFun v:=∑ i,v i • Cg i
  map_add' := by intros; simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,←smul_smul,RingHom.id_apply]

lemma wand_eq (v) : wand v=∑ i, v i • Cg i := rfl

lemma wand_trip (u v w : Quint) : (wand u * wand v * wand w).trace=0 := by
  simp only [wand_eq,Matrix.mul_sum,Matrix.sum_mul,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,Cg_three, smul_zero,sum_const]

lemma wand_square (u : Quint) : wand u * wand u = (u ⬝ᵥ u) • (1:Op SpinIdx) := by
  let F(s : Finset Five):=∑ i∈s,u i • Cg i
  have e s : F s * F s = (∑ i∈s,u i*u i) • (1:Op SpinIdx) := by
    induction s using Finset.induction with
    | empty => simp [F]
    | @insert i s h ih =>
      have z : Cg i* F s= -(F s* Cg i) := by
        unfold F
        rw [Matrix.mul_sum,Matrix.sum_mul, ←sum_neg_distrib]
        exact sum_congr rfl fun j hj=> by rw [Matrix.mul_smul,Matrix.smul_mul,
          Cg_swap (show i≠j from fun w=>h (w.symm ▸ hj)),smul_neg]

      rw [show F (insert i s)=u i• Cg i+F s from sum_insert h,
        sum_insert h,add_mul,mul_add,mul_add,ih]
      simp only [Matrix.mul_smul,Matrix.smul_mul,z,Cg_square,smul_smul,
        smul_neg,add_smul]
      abel
  exact e univ

def tr5 (v w x y z : Quint) := (wand v * wand w * wand x * wand y * wand z).trace

lemma cycle (v w x y z:Quint) : tr5 v w x y z = tr5 w x y z v := by
  simp only [tr5,mul_assoc]
  rw [trace_mul_comm]; simp only [mul_assoc]

lemma tr5_adjacent (a b c d:Quint) : tr5 a a b c d=0 := by
  have w:=wand_trip b c d
  simp only [tr5,wand_square,Matrix.smul_mul,one_mul,trace_smul,w,smul_zero]

lemma tr5_leap (a b c d:Quint) : tr5 a b a c d=0 := by
  have e : wand a * wand b = (((a+b) ⬝ᵥ (a+b))-a⬝ᵥa-b⬝ᵥb) • 1 - wand b * wand a := by
    rw [sub_smul,sub_smul, ←wand_square,←wand_square,←wand_square, map_add,
      add_mul,mul_add,mul_add]; abel

  rw [tr5,e,sub_mul,sub_mul,sub_mul,trace_sub, show _=tr5 b a a c d from (rfl : (wand b * wand a * wand a * wand c * wand d).trace=_), cycle, tr5_adjacent]
  simp only [Matrix.smul_mul,one_mul,trace_smul,wand_trip,smul_zero,sub_zero]

private def chantF : MultilinearMap ℂ (fun _:Five => Quint) ℂ :=
  (Matrix.traceLinearMap SpinIdx ℂ ℂ).compMultilinearMap
    ((MultilinearMap.mkPiAlgebraFin ℂ 5 (Op SpinIdx)).compLinearMap (fun _ => wand))

private lemma chantF_eq (v: Five→Quint) :
    chantF v=tr5 (v 0) (v 1) (v 2) (v 3) (v 4) := by
  change ((MultilinearMap.mkPiAlgebraFin ℂ 5 (Op SpinIdx)) (fun i=>wand (v i))).trace= _
  rw [MultilinearMap.mkPiAlgebraFin_apply]
  simp only [List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one,tr5,mul_assoc]
  rfl

set_option maxHeartbeats 2000000 in
private def chant : Quint [⋀^Five]→ₗ[ℂ] ℂ where
  toMultilinearMap := chantF
  map_eq_zero_of_eq' v i j h e := by
    change chantF v=0
    rw [chantF_eq]
    fin_cases i <;> fin_cases j <;> try exact (e rfl).elim
    -- h indices defeq but elaborated as ctor, no rw literals change
    · rw [show v 0=v 1 from h, tr5_adjacent]
    · rw [show v 0=v 2 from h, tr5_leap]
    · rw [show v 0=v 3 from h, cycle, cycle, cycle, tr5_leap]
    · rw [show v 0=v 4 from h, cycle, cycle, cycle, cycle, tr5_adjacent]
    · rw [show v 1=v 0 from h, tr5_adjacent]
    · rw [show v 1=v 2 from h, cycle, tr5_adjacent]
    · rw [show v 1=v 3 from h, cycle, tr5_leap]
    · rw [show v 1=v 4 from h, cycle, cycle, cycle, cycle, tr5_leap]
    · rw [show v 2=v 0 from h, tr5_leap]
    · rw [show v 2=v 1 from h, cycle, tr5_adjacent]
    · rw [show v 2=v 3 from h, cycle, cycle, tr5_adjacent]
    · rw [show v 2=v 4 from h, cycle, cycle, tr5_leap]
    · rw [show v 3=v 0 from h, cycle, cycle, cycle, tr5_leap]
    · rw [show v 3=v 1 from h, cycle, tr5_leap]
    · rw [show v 3=v 2 from h, cycle, cycle, tr5_adjacent]
    · rw [show v 3=v 4 from h, cycle, cycle, cycle, tr5_adjacent]
    · rw [show v 4=v 0 from h, cycle, cycle, cycle, cycle, tr5_adjacent]
    · rw [show v 4=v 1 from h, cycle, cycle, cycle, cycle, tr5_leap]
    · rw [show v 4=v 2 from h, cycle, cycle, tr5_leap]
    · rw [show v 4=v 3 from h, cycle, cycle, cycle, tr5_adjacent]

lemma wand_single (i:Five) : wand (Pi.single i 1)=Cg i := by
  rw [wand_eq,Finset.sum_eq_single i]
  · simp
  · intro b _ h
    rw [Pi.single_eq_of_ne h,zero_smul]
  simp

private lemma chant_basis : chant (Pi.basisFun ℂ Five)= -4 := by
  change chantF _=_
  rw [chantF_eq,tr5]
  simp only [Pi.basisFun_apply,wand_single]
  have e : Cg 1 * Cg 2 * Cg 3 * Cg 4=grading := by
    rw [mul_assoc (Cg 1 * Cg 2),
      show Cg 1*Cg 2=_ from Cg_pair 0 1,show Cg 3*Cg 4=_ from Cg_pair 2 3,
      ← mul_assoc, ←grading_rule]
  rw [mul_assoc,mul_assoc (Cg 0*Cg 1),mul_assoc (Cg 0),
    ←mul_assoc (Cg 2),←mul_assoc (Cg 1),←mul_assoc (Cg 1),e,Cg_0,
    neg_mul,gradingOne,trace_neg,trace_one]
  simp [SpinIdx]

theorem volume (M : Matrix Five Five ℂ) :
    tr5 (M 0) (M 1) (M 2) (M 3) (M 4) = -4*M.det := by
  rw [←chantF_eq M]
  change chant M = _
  rw [AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ Five) chant,chant_basis,Pi.basisFun_det]
  rfl
