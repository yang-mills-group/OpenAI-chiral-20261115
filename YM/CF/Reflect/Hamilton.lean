import YM.CF.Reflect.Strip

/-! Wilson nearest-neighbor rows, before the splice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Kronecker
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {m B N : Side} (i j : Axis)

def lowB (i : Axis) : Op SpinIdx := (1/2:ℂ) • (1-gammaOp i)
def highB (i : Axis) : Op SpinIdx := (1/2:ℂ) • (1+gammaOp i)
lemma halves_l : gammaOp i*lowB i= -lowB i := by rw [lowB,Algebra.mul_smul_comm, mul_sub,mul_one,gammaOne,←neg_sub 1,smul_neg]
lemma halves_r : gammaOp i * highB i = highB i := by rw [highB,Algebra.mul_smul_comm, mul_add,mul_one,gammaOne, add_comm]
lemma flipCl : lowB i*grading=grading*highB i := by unfold lowB highB; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,sub_mul,mul_add,one_mul,mul_one,gradingSwap]; abel
lemma flipCr : highB i*grading=grading*lowB i := by unfold lowB highB; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,add_mul,mul_sub,one_mul,mul_one,gradingSwap]; abel
lemma Pinlow : pin i * lowB i=grading * lowB i := by rw [pin,mul_assoc,←flipCr,←mul_assoc,halves_r]
lemma Pinhigh : pin i * highB i= -(grading * highB i) := by rw [pin,mul_assoc,←flipCl,←mul_assoc,halves_l,neg_mul]
lemma flatL : star (lowB i)=lowB i := by rw [lowB,star_smul,star_sub,star_one,(gammaAdj i).star_eq]; norm_num
lemma flatR : star (highB i)=highB i := by rw [highB,star_smul,star_add,star_one,(gammaAdj i).star_eq]; norm_num
lemma twol : lowB i*lowB i=lowB i := by
  nth_rw 1 [lowB]; rw [Algebra.smul_mul_assoc, sub_mul, one_mul, halves_l, smul_sub,smul_neg]; module
lemma twor : highB i*highB i=highB i := by nth_rw 1 [highB]; rw [Algebra.smul_mul_assoc, add_mul,one_mul,halves_r,smul_add]; module
-- writing H as onsite + plus orientations.
def Vplus (c : Site N) (U : Bkg N) (i : Axis) := -(spin N Slot (grading * lowB i)*shift matter U c i)
lemma spin_lifts (N : Side) (X Y) : spin N Slot (X-Y)=spin N Slot X-spin N Slot Y := by
  unfold spin; rw [←jump_sub]; congr; funext x; ext i j; simp [sub_mul]
lemma spin_raise (N : Side) (X) (c : ℂ) : spin N Slot (c • X)=c • spin N Slot X := by
  unfold spin; rw [←jump_smul]; apply congrArg; funext x; ext i j; simp [mul_assoc]
lemma real_half (X : Op (Model N)) : (1/2:ℝ) • X=(1/2:ℂ) • X := by ext i j; simp [Complex.real_smul]
lemma collectH (c : Site N) (U : Bkg N) (i : Axis) : (frame matter U c).chir * (frame matter U c).inc i= (frame matter U c).chir+Vplus c U i + star (Vplus c U i) := by
  let C := spin N Slot grading; let b := lowB i; let J := spin N Slot b
  let T := shift matter U c i; let G := spin N Slot (gammaOp i); let Y := star T; let a := (1/2:ℂ)
  have he : C*J=spin N Slot (grading*b) := spin_mul ..
  have hp : star C=C := by unfold C; rw [spin_adj,gradingAdj]
  have hx : star J=J := by unfold J b; rw [spin_adj,flatL]
  have hj : J=a • (1-G) := by unfold J b lowB; rw [spin_raise,spin_lifts,spin_one]
  have hh : star (Vplus c U i) = -(J*C*Y) := by
    unfold Vplus; change star (-(spin N Slot (grading*b)*T))=_
    rw [star_neg,←he,star_mul,star_mul,hx,hp]; apply congrArg Neg.neg
    have hg : Commute (J*C) T := (show Commute J T from spin_shift matter U c _ _).mul_left (spin_shift matter U c _ _)
    have hg' : T*(C*J)=(C*J)*T := show T*_=_ from (show Commute (C*J) T from (show Commute C T from spin_shift ..).mul_left (spin_shift ..)).symm.eq
    have hT := congrArg star hg'; rw [star_mul,star_mul (C*J),star_mul,hx,hp] at hT; exact hT.symm
  rw [hh]; unfold Vplus WilsonFrame.inc WilsonFrame.diff WilsonFrame.lap
  change C*(1-(1/2:ℝ) • (T+Y)+G*((1/2:ℝ) • (T-Y)))=C+ -(spin N Slot (grading*b)*T) + _
  rw [←he,hj]; rw [real_half, real_half]; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_add,mul_sub,sub_mul,mul_one,one_mul]
  have hk : C*G= -(G*C) := by unfold C G; rw [spin_mul, gradingSwap, spin_neg,spin_mul]
  simp only [mul_sub,mul_one,←mul_assoc];
  -- need tuning
  simp only [hk,neg_mul,smul_sub,smul_neg,smul_add,a]; abel
theorem supportH (c : Site N) (U : Bkg N) :
    (frame matter U c).H=(3:ℂ) • spin N Slot grading + ∑ i:Axis,(Vplus c U i+star (Vplus c U i)) := by
  let C := spin N Slot grading
  simp only [WilsonFrame.H,WilsonFrame.H0,mul_add,mul_neg,mul_one,mul_sum, collectH,add_assoc] -- tune
  simp only [Axis,sum_add_distrib,sum_const,card_univ,Fintype.card_fin]
  change -C + (4 • C + _)=(3:ℂ) • C + _; rw [←add_assoc]; congr 1; module
lemma plus_block (c : Site N) (U : Bkg N) i : Vplus c U i=jump (advance i) (fun x=> -(((grading*lowB i) ⊗ₖ 1)*hop matter U c i x)) := by
  unfold Vplus spin shift; rw [jump_mul]; simp only [Equiv.refl_trans,Equiv.refl_apply]; rw [jump_neg]
def Ledge (m B : Side) (i : Axis) : Op (Model (CSide m B)) := cutM (colony m B i)
def Tedge (m B : Side) (i : Axis) : Op (Model (CSide m B)) := cutM (colony m B i)ᶜ
lemma etp : Tedge m B i=1-Ledge m B i := dim_cut _
lemma trayH (U : Skin m B) (c : Phase.Part m B) : (Ledge m B i*(wiel m B c U)*Ledge m B i).trace=0 := by
  let P := Ledge m B i; let X := (3:ℂ) • (spin (CSide m B) Slot grading)
  have hd j (t : Xmind m B) : Vplus c (links U) j t t=0 := by
    have he : advance j t.1≠t.1 := by
      intro h; have hp : t.1 j+1=t.1 j := by simpa [advance] using congr_fun h j -- tune
      have hq := add_eq_left.mp hp; have hk := suff_pos m B; haveI : Fact (1 < (CSide m B).val) := ⟨hk⟩; exact one_ne_zero (α:=Per (CSide m B)) hq
    rw [plus_block,jump_apply,if_neg he]
  have hk t : wiel m B c U t t=X t t := by rw [wiel,supportH,Matrix.add_apply,Matrix.sum_apply,sum_eq_zero,add_zero]; intro j _; simp [hd j t]
  have hz (t : Xmind m B) : (P*wiel m B c U*P) t t= if t.1∈posY m B i then 3*(grading t.2.1 t.2.1) else 0 := by
    unfold P Ledge cutM; rw [Matrix.mul_diagonal, Matrix.diagonal_mul,hk]; by_cases h:t∈colony m B i
    · simp [h,(colony_at t i).mp h,X,spin,jump_apply]
    simp [h,show t.1∉_ from fun g=>h ((colony_at t i).mpr g)] -- tune
  rw [Matrix.trace]; change ∑ t:Xmind m B,(P*wiel m B c U*P) t t=0
  simp_rw [hz]; rw [Fintype.sum_prod_type]; apply sum_eq_zero; intro x _
  by_cases h:x∈ posY m B i; simp_rw [if_pos h]; rw [Fintype.sum_prod_type]; simp [grading,SpinIdx,Fin.sum_univ_succ]; ring -- tune
  simp_rw [if_neg h,sum_const_zero]
end YM.CF.RP
