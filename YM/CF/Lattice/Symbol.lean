import YM.CF.Lattice.Overlap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
/-! No free doublers in the bare overlap kinetic symbol. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BZ
open WilsonFrame Finset
open scoped Matrix.Norms.L2Operator Matrix BigOperators Topology MatrixOrder
attribute [local instance] opCStarAlgebra
abbrev Mom := Fin 4 → ℝ

def phase (x : ℝ) := Complex.exp (x*Complex.I)
lemma phase_one (x : ℝ) : phase x * star (phase x)=1 := by
  simp [phase, ← Complex.exp_conj,← Complex.exp_add]
def atom (p : Mom) : WilsonFrame SpinIdx where
  T i := phase (p i) • 1
  gamma := gammaOp
  chir := grading
  shiftU i := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [star_smul,star_one,Algebra.smul_mul_assoc,one_mul,smul_smul,phase_one,one_smul]
  gammaSA := gammaAdj
  chirSA := gradingAdj
  gammaSq := gammaOne
  chirSq := gradingOne
  cliff := gammaSwap
  graded := gradingSwap
  spins i j := (Commute.one_right _).smul_right _
  signs i := (Commute.one_right _).smul_right _
lemma atomGap (p : Mom) : (1:Op SpinIdx) ≤ (atom p).H^2 := by
  have hs i j : Switch ((atom p).T i) ((atom p).T j) 0 := Switch.fromCommute ((Commute.one_left _).smul_left (phase (p i)))
  simpa using (atom p).gap (fun i j _ => hs i j)
lemma atom_safe (p : Mom) : Safe (atom p).H := by
  refine ⟨(atom p).selfadjoint,(atom p).bounded.trans (by norm_num), le_trans ?_ (atomGap p)⟩
  calc
    _ ≤ (1:ℝ) • (1:Op SpinIdx) := smul_le_smul_of_nonneg_right (by norm_num) zero_le_one
    _ = _ := one_smul ..
lemma phase_eval (x : ℝ) : phase x = (Real.cos x:ℂ) + Complex.I * Real.sin x := by
  rw [phase,Complex.exp_mul_I]; simp [mul_comm]
lemma mean (x : ℝ) : (1/2:ℝ) • (phase x+star (phase x))=(Real.cos x:ℂ) := by
  rw [phase_eval]; simp [Complex.ext_iff,Complex.add_re,Complex.add_im]
  all_goals ring
def slash (p : Mom) := ∑ i, Real.sin (p i) • (Complex.I • gammaOp i)
def bare (p : Mom) := -1 + ∑ i, (1-Real.cos (p i))
def wave (p : Mom) := Real.sqrt (bare p ^ 2 + ∑ i, Real.sin (p i) ^ 2)

lemma half_diff (x:ℝ) : (1/2:ℝ) • (phase x-star (phase x))=Real.sin x • Complex.I := by
  rw [phase_eval]; simp [Complex.ext_iff,Complex.add_re,Complex.add_im]
  all_goals ring
lemma ofReal_action (x:ℝ) (v:Op SpinIdx) : (x:ℂ) • v = x • v := (RCLike.real_smul_eq_coe_smul ..).symm -- check
lemma atom_l (p : Mom) (i) : (atom p).lap i=(1-Real.cos (p i)) • (1:Op SpinIdx) := by
  simp only [lap, atom,star_smul,star_one]
  rw [← add_smul,← smul_assoc,mean, ofReal_action, sub_smul, one_smul]
lemma atom_s (p : Mom) (i) : (atom p).diff i=Real.sin (p i) • (Complex.I • (1:Op SpinIdx)) := by
  simp only [diff,atom,star_smul,star_one]
  rw [← sub_smul,← smul_assoc,half_diff, smul_assoc]
lemma atom_H0 (p : Mom) : (atom p).H0=bare p • (1:Op SpinIdx)+slash p := by
  simp only [H0,inc,atom_l,atom_s,Algebra.mul_smul_comm,mul_one,bare,slash,sum_add_distrib,add_smul,
    sum_smul,neg_smul,one_smul]; rw [add_assoc]; rfl
lemma slash_star (p : Mom) : star (slash p)= -slash p := by
  unfold slash; rw [star_sum, ← sum_neg_distrib]
  apply sum_congr rfl; intro i _; simp only [star_smul, star_trivial,(gammaAdj i).star_eq,
    show star Complex.I= -Complex.I from Complex.conj_I, neg_smul,smul_neg]
lemma slash_anticomm (p : Mom) : grading * slash p= -(slash p*grading) := by
  unfold slash; rw [Matrix.mul_sum,Matrix.sum_mul,← sum_neg_distrib]
  apply sum_congr rfl; intro i _; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,gradingSwap,smul_neg]
lemma slash_sq (p : Mom) : slash p * slash p = -((∑ i, Real.sin (p i)^2) • (1:Op SpinIdx)) := by
  let S i := Real.sin (p i) • (Complex.I • gammaOp i)
  have ht (u : Finset (Fin 4)) : (∑ i∈u, S i)*(∑ i∈u, S i) = -((∑ i∈u,Real.sin (p i)^2) • (1:Op SpinIdx)) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih =>
      rw [sum_insert hi,sum_insert hi, add_mul, mul_add, mul_add,ih, Matrix.sum_mul,Matrix.mul_sum]
      rw [show S i*S i= -(Real.sin (p i)^2 • (1:Op SpinIdx)) by
        unfold S; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,
          gammaOne,smul_smul,smul_smul,Complex.I_mul_I,neg_one_smul,sq,smul_neg]]
      have he (j) (hj:j∈u) : S j * S i= -(S i*S j) := by
        unfold S; have hm : j≠i := fun h => hi (h ▸ hj)
        simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc, gammaSwap j i hm,smul_neg]
        module
      rw [show ∑ j∈u,S j*S i= -∑ j∈u,S i*S j by rw [← sum_neg_distrib]; exact sum_congr rfl he, add_smul]; abel
  exact ht _
lemma atom_square (p : Mom) : (atom p).H*(atom p).H=(wave p)^2 • (1:Op SpinIdx) := by
  rw [(atom p).H_square,atom_H0,star_add,slash_star,star_smul,star_trivial,star_one,add_mul,mul_add,mul_add,
    neg_mul,neg_mul,slash_sq] -- check
  have hs : 0 ≤ bare p^2+∑ i, Real.sin (p i)^2 := by positivity
  simp only [wave,Real.sq_sqrt hs,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,one_mul]
  module
lemma wave_pos (p : Mom) : 0 < wave p := by
  have hp : 0 ≤ wave p := Real.sqrt_nonneg ..
  by_contra! h
  have hg := atomGap p; rw [sq, atom_square, le_antisymm h hp] at hg
  norm_num at hg
  exact one_ne_zero (le_antisymm hg zero_le_one)
lemma atomS (p : Mom) : polarity (atom p).H=(wave p)⁻¹ • (atom p).H :=
  polarity_scalar (atom_safe p) _ (wave_pos _).le (atom_square _)
lemma grading_pol (p : Mom) : grading*polarity (atom p).H + polarity (atom p).H*grading =
    (2*(bare p/wave p)) • 1 := by
  rw [atomS,H, atom_H0]
  simp only [show (atom p).chir = grading from rfl,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    ← mul_assoc grading grading, gradingOne,one_mul]
  simp only [mul_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,add_mul,mul_one, gradingOne]
  rw [slash_anticomm]; simp only [neg_mul, mul_assoc,gradingOne,mul_one]
  simp only [div_eq_mul_inv]
  module

def scale (p : Mom) : ℝ := 1/2*(1+bare p/wave p)
def Zone (p : Mom) := ∀ i, -Real.pi < p i ∧ p i ≤ Real.pi
lemma scale_pos (p) (hp : Zone p) (h : p ≠ 0) : 0 < scale p := by
  have he := wave_pos p
  have hs : wave p ^ 2 = bare p ^ 2 + ∑ i, Real.sin (p i)^2 := Real.sq_sqrt (by positivity)
  apply mul_pos (by norm_num) ?_
  suffices H : -1 < bare p / wave p by linarith
  rw [lt_div_iff₀ he]; by_cases H : ∃ i, Real.sin (p i)≠0
  · obtain ⟨i,hi⟩ := H
    have hd : 0 < ∑ i, Real.sin (p i)^2 := Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩
    nlinarith
  push Not at H
  have hv : ∃ i,p i ≠ 0 := by by_contra! hh; exact h (funext hh)
  obtain ⟨i,hi⟩ := hv
  have hx : p i=Real.pi := eq_of_le_of_not_lt (hp _).2 (fun hh => hi ((Real.sin_eq_zero_iff_of_lt_of_lt (hp i).1 hh).mp (H i)))
  have ht := Finset.single_le_sum (f:=fun i => 1-Real.cos (p i))
    (fun i _ => sub_nonneg.mpr (Real.cos_le_one _)) (Finset.mem_univ i)
  -- rewrite only single-term, beware all occurrences
  rw [hx,Real.cos_pi] at ht
  unfold bare; linarith

private lemma sandwich {A B : Op SpinIdx} {r : ℝ} (hx : A*A=1)
    (h : A*B+B*A=(2*r) • 1) :
    let X := (1/2 : ℝ) • (1+A)
    X*((1/2 : ℝ) • (1+B))*X=(1/2*(1+r)) • X := by
  intro X
  have hb := congrArg (fun C:Op SpinIdx => C*A) h
  change (A*B+B*A)*A=((2*r) • 1)*A at hb
  rw [add_mul,mul_assoc B,hx,mul_one,Algebra.smul_mul_assoc,one_mul] at hb
  dsimp only [X]
  simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_add,add_mul,one_mul,mul_one,hx]
  rw [show A*B*A = (2*r) • A-B from eq_sub_of_add_eq hb,
    show A*B=(2*r) • (1:Op SpinIdx)-B*A from eq_sub_of_add_eq h]
  module
lemma compress (p : Mom) :
    let A := (atom p).plus; let P := projector (atom p).H
    A*P*A = scale p • A ∧ P*A*P=scale p • P :=
  ⟨sandwich gradingOne (grading_pol _), sandwich (atom_safe _).polar_square (by
    rw [add_comm]; exact grading_pol p)⟩
lemma inverseMode (p : Mom) (h : Zone p) (hp : p≠0) :
    let A := (atom p).plus; let P := projector (atom p).H; let K := (atom p).overlap*P; let J := (scale p)⁻¹ • (P*A)
    K*J=A ∧ J*K=P := by
  intro A P K J
  obtain ⟨he,hf⟩ := compress p
  have ha : A*A=A := (atom p).plusSq
  have hb : P*P=P := (atom_safe p).projection.1
  have hk : K=A*P := (atom p).overlap_action (atom_safe p)
  change A*P*A=_ at he; change P*A*P=_ at hf
  have hh := (scale_pos p h hp).ne'
  simp only [J,hk,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_assoc,← mul_assoc P P,
    hb,← mul_assoc A A,ha, show A*(P*A)=scale p • A by rw [← mul_assoc,he],
    show P*(A*P)=scale p • P by rw [← mul_assoc,hf],inv_smul_smul₀ hh, and_self]

lemma origin : let W := atom 0; projector W.H=1-W.plus ∧ W.overlap * projector W.H=0 := by
  intro W
  have hh : W.H= - W.chir := by
    rw [H]; dsimp only [W]; rw [atom_H0]; simp [bare, slash]
  have hP : projector W.H=1-W.plus := by
    rw [projector,show polarity W.H=(wave 0)⁻¹ • W.H from atomS _, hh,
      show wave 0=1 by simp [wave,bare], inv_one,one_smul, plus]
    module
  refine ⟨hP,?_⟩
  rw [W.overlap_action (atom_safe _), hP,mul_sub, mul_one,W.plusSq,sub_self]
end YM.CF.BZ
