import YM.CF.Fixed.EnergyCross
import YM.CF.Fixed.Seam
import YM.CF.Lattice.Frequencies
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Fiber with spatial Fourier only; temporal seam still through zero (actual
`anticut`). Here Axis 0. Same orientation usual by changing coordinates later. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll Bulk
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

abbrev Spin := Op SpinIdx
def plusS:Spin:= (1/2:ℝ) • (1+gammaOp 0)
def minusS:Spin:=1-plusS
lemma opp_s : minusS=(1/2:ℝ) • (1-gammaOp 0):=by unfold minusS plusS; module
lemma plus_ok:IsStarProjection plusS:= by
  constructor
  · change plusS * plusS= _; unfold plusS; simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,mul_add,add_mul, gammaOne,mul_one,one_mul]; module
  unfold plusS; exact IsSelfAdjoint.smul (.all _) ((IsSelfAdjoint.one _).add (gammaAdj _))
lemma minus_ok : IsStarProjection minusS:=plus_ok.one_sub

def incoming:Spin:= -(grading*minusS)
lemma pm_g : grading*plusS=minusS*grading:= by unfold plusS; rw [opp_s]; simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_add, sub_mul, gradingSwap, one_mul,mul_one]; rw [sub_eq_add_neg]
lemma mg_p: grading*minusS=plusS*grading:=by unfold minusS plusS; simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_sub,mul_add,add_mul, mul_one,one_mul,gradingSwap]; module
lemma exit_star: star incoming = -(grading*plusS) := by rw [incoming,star_neg,star_mul,gradingAdj.star_eq,minus_ok.isSelfAdjoint.star_eq,pm_g]
lemma incoming_link: star incoming*incoming=minusS:=by unfold incoming; rw [star_neg,star_mul,gradingAdj.star_eq,minus_ok.isSelfAdjoint.star_eq,neg_mul_neg,mul_assoc, ←mul_assoc grading,gradingOne,one_mul]; exact minus_ok.isIdempotentElem -- maybe `.pow_eq` accel
lemma outgoing_link: incoming * star incoming=plusS:=by rw [exit_star,incoming,mg_p,neg_mul_neg,mul_assoc plusS,←mul_assoc grading,gradingOne,one_mul]; exact plus_ok.isIdempotentElem
lemma incoming_nil: incoming * incoming =0:=by unfold incoming; rw [neg_mul_neg,←mul_assoc, mul_assoc grading,←pm_g,←mul_assoc grading,gradingOne,one_mul]; unfold minusS; rw [mul_sub,mul_one,plus_ok.isIdempotentElem,sub_self]
lemma exit_nil: star incoming*star incoming=0:=by rw [←star_mul,incoming_nil,star_zero]
lemma in_top : incoming * (-pin 0) = -plusS:=by
  unfold incoming pin; rw [neg_mul_neg,mg_p,mul_assoc,←mul_assoc grading, gradingSwap, neg_mul,mul_assoc (gammaOp 0),gradingOne,mul_one,mul_neg]; unfold plusS; simp only [Algebra.smul_mul_assoc,add_mul,one_mul,gammaOne]; module
lemma in_base : (-star incoming) * (-pin 0) = -minusS:=by rw [exit_star, neg_neg]; unfold pin; rw [pm_g,mul_neg,mul_assoc,← mul_assoc grading, gradingSwap,neg_mul, mul_assoc (gammaOp 0),gradingOne,mul_one, mul_neg,neg_neg]; rw [opp_s]; simp only [Algebra.smul_mul_assoc,sub_mul, gammaOne,one_mul]; module
lemma flip_fw: pin 0*incoming*(-pin 0)= -(star incoming):=by rw [mul_assoc, in_top,exit_star,neg_neg]; unfold pin; rw [mul_neg]; unfold plusS; simp only [Algebra.mul_smul_comm,mul_add,mul_one, gradingSwap]; rw [mul_assoc (gammaOp 0),gradingSwap,mul_neg,←mul_assoc,gammaOne,one_mul]; module
lemma flip_bw: pin 0 * star incoming * (-pin 0)= -incoming:=by have he := congrArg star (flip_fw); simp only [star_neg,star_star, star_mul,pinS,neg_neg] at he; rw [mul_assoc]; exact he

def angleM (j:Fin 3):Spin:= Complex.I • (grading * gammaOp j.succ)
lemma angle_sq (i:Fin 3): angleM i*angleM i=1:=by unfold angleM; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,Complex.I_mul_I]; rw [neg_one_smul,mul_assoc, show gammaOp i.succ * (grading*gammaOp i.succ)= -grading from (by rw [←mul_assoc,show gammaOp i.succ*grading= -(grading*gammaOp i.succ) from (by rw [gradingSwap,neg_neg]),neg_mul,mul_assoc,gammaOne,mul_one])]; rw [mul_neg,gradingOne,neg_neg] -- tune
lemma angle_adj (i:Fin 3): IsSelfAdjoint (angleM i) :=by rw [isSelfAdjoint_iff,angleM,star_smul, star_mul,gradingAdj.star_eq,(gammaAdj _).star_eq, show star Complex.I = -Complex.I from Complex.conj_I]; rw [gradingSwap,smul_neg,neg_smul] -- occurrence
lemma spin_turn (j:Fin 3): pin 0 * gammaOp j.succ= gammaOp j.succ * pin 0:=by rw [pin,mul_assoc,gradingSwap,mul_neg,←mul_assoc,gammaSwap 0 j.succ (Ne.symm (Fin.succ_ne_zero _)),neg_mul,neg_neg,mul_assoc]
lemma spin_turn_g : pin 0 * grading= - (grading * pin 0):=by rw [pin, ←mul_assoc grading, gradingSwap,neg_mul,neg_neg]
lemma magnetic (j:Fin 3): pin 0*angleM j= -(angleM j*pin 0):=by unfold angleM; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,←mul_assoc,spin_turn_g, neg_mul, mul_assoc grading,spin_turn,←mul_assoc grading,smul_neg]

lemma grade_norm: ‖grading‖=1:= CStarRing.norm_of_mem_unitary (by constructor <;> rw [gradingAdj.star_eq,gradingOne])
lemma spatial_norm(j:Fin 3): ‖angleM j‖=1:= CStarRing.norm_of_mem_unitary (by constructor <;> rw [(angle_adj _).star_eq,angle_sq])
abbrev Three:=Fin 3→ℝ
def varS (i:Fin 3)(x:ℝ):Spin := (1-Real.cos x) • grading + Real.sin x • angleM i
def phaseS (x:Three):Spin:= ∑ i,varS i (x i)
lemma flip_vS (i:Fin 3)(x:ℝ): pin 0* varS i x= -(varS i x*pin 0):=by unfold varS; rw [mul_add,add_mul, Algebra.mul_smul_comm, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,spin_turn_g,magnetic]; simp [add_comm]
lemma flip_spin (x:Three): pin 0*phaseS x * (-pin 0)= -phaseS x:= by
  unfold phaseS; simp only [Matrix.mul_sum,Matrix.sum_mul, flip_vS,neg_mul_neg, mul_assoc,pin_square]; simp [Finset.sum_neg_distrib]
lemma varS_self (i)(x): IsSelfAdjoint (varS i x):= IsSelfAdjoint.add (IsSelfAdjoint.smul (.all _) gradingAdj) (IsSelfAdjoint.smul (.all _) (angle_adj _))
lemma phase_self(x): IsSelfAdjoint (phaseS x) := by rw [isSelfAdjoint_iff,phaseS,star_sum]; exact Finset.sum_congr rfl fun _ _=>(varS_self _ _).star_eq
@[simp] lemma varS0(i):varS i 0=0:=by unfold varS; simp
@[simp] lemma phase_zero: phaseS 0=0:=by simp [phaseS]
lemma diff_vS(i)(x y:ℝ): ‖varS i x-varS i y‖≤ 2*|x-y|:=by
  unfold varS; rw [add_sub_add_comm,← sub_smul,←sub_smul]; refine le_trans (norm_add_le ..) ?_; rw [norm_smul,norm_smul,grade_norm,spatial_norm,mul_one,mul_one]; rw [show 1-Real.cos x-(1-Real.cos y)=Real.cos y-Real.cos x from by abel, norm_sub_rev, Real.norm_eq_abs, Real.norm_eq_abs]; linarith [Real.abs_sin_sub_sin_le x y,Real.abs_cos_sub_cos_le x y]
lemma small_vS (i)(x:ℝ): ‖varS i x‖ ≤ 2*|x|:= by simpa using diff_vS i x 0
lemma small_phase (x:Three) (z:ℝ)(p:∀ i,|x i|≤z): ‖phaseS x‖ ≤ 6*z:=by exact le_trans (norm_sum_le ..) ((sum_le_sum (g:=fun _=> 2*z) (fun i _=> (small_vS ..).trans (mul_le_mul_of_nonneg_left (p i) (by norm_num)))).trans (by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; linarith) )
lemma differ (x:Three) (z:ℝ) : phaseS (update x 0 (x 0 +z)) = phaseS x + (varS 0 (x 0+z)-varS 0 (x 0)):=by unfold phaseS; rw [Fin.sum_univ_succ, Fin.sum_univ_succ (n:=2) (f:=fun i:Fin 3=>varS i (x i))]; simp_rw [update_self, update_of_ne (Fin.succ_ne_zero _)]; abel

-- exact trace cross (uses primary physical spatial direction 1)
lemma angle_g (i:Fin 3): angleM i*grading= -(grading*angleM i):=by
  unfold angleM; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,← mul_assoc grading,gradingOne]; rw [gradingSwap,neg_mul, mul_assoc,gradingOne]; simp
lemma angle_com (i:Fin 3) : gammaOp 0 * angleM i= angleM i * gammaOp 0:=by unfold angleM; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; congr 1; rw [←mul_assoc]; rw [show gammaOp 0*grading= -(grading*gammaOp 0) from (by rw [gradingSwap,neg_neg]),neg_mul,mul_assoc,gammaSwap 0 i.succ (Ne.symm (Fin.succ_ne_zero _)),mul_neg,neg_neg,←mul_assoc]
lemma angle_forward(i:Fin 3) : angleM i*incoming= -(incoming*angleM i) := by
  unfold incoming; rw [mul_neg, ← mul_assoc, angle_g, neg_mul,neg_neg, neg_mul, neg_neg]; rw [mul_assoc,mul_assoc]; congr 1; rw [opp_s]; simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,mul_sub,mul_one, sub_mul,one_mul,angle_com]
lemma angle_backward(i): star incoming*angleM i= -(angleM i*star incoming):=by have he := congrArg star (angle_forward i); rw [star_mul,star_neg,star_mul,(angle_adj _).star_eq] at he; exact he
lemma tr_minus : trR minusS=2:=by unfold trR; rw [opp_s]; simp [Matrix.trace,Matrix.diag,gammaOp,SpinIdx,Fin.sum_univ_succ,Complex.real_smul]; norm_num
lemma g_in : grading*incoming= -minusS:=by unfold incoming; rw [mul_neg, ←mul_assoc,gradingOne,one_mul]
lemma gfw : grading*star incoming=incoming*grading:=by rw [exit_star,incoming,mul_neg,←mul_assoc grading,gradingOne,mg_p,neg_mul,mul_assoc plusS,gradingOne]; simp
lemma winter(A B:ℝ)(i:Fin 3) : let M : Spin := A • grading+B • angleM i; trR (M*star incoming*M*incoming) = -2*B^2:=by
  intro M; have he:grading *star incoming*grading*incoming=0:=by rw [gfw,mul_assoc incoming,gradingOne,mul_one,incoming_nil]
  have hq:trR (grading*star incoming*angleM i*incoming)=0:=by rw [comm_t _ incoming, ←mul_assoc,← mul_assoc,←gfw] -- f*grading→g f*
                                                              rw [mul_assoc grading,exit_nil, mul_zero,zero_mul]; simp [trR]
  have hp:trR (angleM i*star incoming*grading*incoming)=0:=by
    have hu:star incoming*grading=grading*incoming:= by rw [exit_star,pm_g,neg_mul,mul_assoc,gradingOne,mul_one, g_in]
    rw [mul_assoc (angleM i) (star incoming),hu,mul_assoc (angleM i),mul_assoc grading,incoming_nil]; simp [trR]
  have hh:angleM i*star incoming*angleM i*incoming= -minusS:=by rw [mul_assoc (angleM i) (star incoming),angle_backward,mul_neg, ←mul_assoc,angle_sq,one_mul,neg_mul,incoming_link]
  unfold M; simp only [add_mul,mul_add,plus_t,Algebra.smul_mul_assoc, Algebra.mul_smul_comm,scale_t,he,hq,hp,hh,debit_t,tr_minus, show trR (0:Spin)=0 from by simp [trR]]; ring -- simp
end YM.CF.Fixed.Rift
