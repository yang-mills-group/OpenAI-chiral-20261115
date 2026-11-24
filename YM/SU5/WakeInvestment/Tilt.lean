import YM.SU5.WakeInvestment.Shear

/-!
*Pointwise* estimate (F -> WA) through not only the normalization projection but also the
positive generator N. Essential: errors are in the price of the difference of projections,
**not** proportional to the dimension of the Fock space, and do not require a uniform
operator-norm bound on the shear family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Fock Lattice Finset NormedSpace
open Papyrus Papyrus.Franc
open Lat Fir Ember Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I : Type*} [LinearOrder I] [Fintype I]
variable {P Q : Op I} {S : Shaft I} {E : ℝ}

def tiltShaft (Q : Op I) (t : ℝ) : Shaft I where
  sell := oneTilt Q t
  buy := oneTilt Q (-t)
  payment := oneTilt_inverse Q t

def weighted (Q : Op I) (t : ℝ) (S : Shaft I) := (tiltShaft Q t).foldC S

lemma tilt_act {Q : Op I} (q : IsStarProjection Q) (t : ℝ) (S : Shaft I) (x : Wave I) :
    acts (wholeTilt Q t) (acts (quant S.sell) x) =
      Real.exp (t*Q.trace.re) • acts (quant (weighted Q t S).sell) x := by
  rw [tilt_spec q,realScalarActs,←act_mul,←quant_mul]; rfl

lemma whole_glow (q : IsStarProjection Q) (S : Shaft I) (F : FC I) (t : ℝ) :
    wholeTilt Q t * (S.glow F) * wholeTilt Q (-t)=(weighted Q t S).glow F := by
  rw [weighted, Shaft.fold_use, tilt_spec q, tilt_spec q]
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,
    ←Real.exp_add,neg_mul,neg_add_cancel, Real.exp_zero,one_smul]; rfl

/-- Constants adequate up to `|t|≤1`, not asserting sharpness. -/
def tiltBound : ℝ := 2*Real.exp 1
lemma tiltBound_pos : 0 < tiltBound := by unfold tiltBound; positivity

lemma sells (q : IsStarProjection Q) (e : ColumnDeal S.sell E) (t : ℝ) (v : |t| ≤ 1) :
    ColumnDeal (weighted Q t S).sell (tiltBound * E) := by
  constructor; intro i; rw [weighted, Shaft.foldC, act_mul]; unfold tiltShaft
  apply (ContinuousLinearMap.le_opNorm ..).trans; unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM]; refine mul_le_mul ((oneTilt_cap q t).trans ?_) (e.all i) (norm_nonneg _) tiltBound_pos.le
  unfold tiltBound; gcongr

lemma buys (q : IsStarProjection Q) (e : ColumnDeal (star S.buy) E) (t : ℝ) (v : |t| ≤ 1) :
    ColumnDeal (star (weighted Q t S).buy) (tiltBound * E) := by
  have h := sells (S:=S.mirrorC) q e (-t) ((abs_neg t) ▸ v)
  change ColumnDeal (star (S.buy * oneTilt Q (-t))) _
  rw [star_mul, (oneTilt_self q _).star_eq]; exact h

/-- Avoid computing any rank cost in the Sea continuation. -/
def vertical (S : Shaft I) (t : ℝ) : Shaft I where
  sell := Real.exp t • S.sell
  buy := Real.exp (-t) • S.buy
  payment := by
    rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,S.payment, smul_smul,
      ←Real.exp_add, neg_add_cancel, Real.exp_zero,one_smul]

lemma vertical_stays (q : IsStarProjection Q) (S : Shaft I) (t : ℝ) (h : S.sell * Q=Q) :
    (vertical (weighted Q t S) t).sell * Q=Q := by
  unfold vertical weighted tiltShaft Shaft.foldC; simp only;
  rw [Algebra.smul_mul_assoc,mul_assoc _,h,left_project q,smul_smul,
    ←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]

lemma vertical_sells (e : ColumnDeal S.sell E) (t : ℝ) :
    ColumnDeal (vertical S t).sell (Real.exp t * E) := by
  constructor; intro i; rw [vertical,realScalarActs,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul_of_nonneg_left (e.all _) (Real.exp_pos _).le

omit [LinearOrder I] in
lemma abs_real_trace (Q : Op I) : |Q.trace.re| ≤ revE Q := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _
  exact single_le_sum (s:=univ) (f:=fun j=> ‖Q i j‖) (fun _ _=> norm_nonneg _) (mem_univ i)

/-- $C(E)$ independent of *all* reg sizes and data. -/
def shellRent (E : ℝ) := (1 + ((Real.exp 1 * (tiltBound * E))^2+1)/2)

lemma TiltSea (p : IsStarProjection P) (q : IsStarProjection Q) (h : S.sell * Q=Q)
    (he : 0 ≤ E) (e : ColumnDeal S.sell E) (x : Wave I) (hx : Sea P x) (t : ℝ) (v : |t| ≤ 1) :
    ‖acts (wholeTilt Q t) (acts (quant S.sell) x)‖ ≤ Real.exp (shellRent E * revE (P-Q)) := by
  let U:= weighted Q t S
  let T:= vertical U t
  let f:= Real.exp t
  let a:= tiltBound * E
  let d := revE (P-Q)
  let m := (((Real.exp 1 * a)^2 + 1)*d/2)
  have ha:0≤a:=mul_nonneg tiltBound_pos.le he
  have hf:0<f:=Real.exp_pos _
  have hz: ColumnDeal T.sell (Real.exp 1*a):= ColumnDeal.more _ (vertical_sells (sells q e t v) t) (mul_le_mul_of_nonneg_right (Real.exp_monotone ((le_abs_self t).trans v)) ha)
  have hy : ‖acts (quant T.sell) x‖ ≤ Real.exp m := sea_gain Q P T x _ p q hx hz (vertical_stays q S t h)
  let u:= Matrix.trace Q |>.re; let l:= Matrix.trace P |>.re
  rw [tilt_act q]; change ‖Real.exp (t*u) • acts (quant U.sell) x‖ ≤ _
  have hX : t*(u-l) ≤ d := by
    apply (le_abs_self _).trans; rw [abs_mul,abs_sub_comm]; unfold l u; rw [←Complex.sub_re,←Matrix.trace_sub]
    exact (mul_le_of_le_one_left (abs_nonneg _) v).trans (abs_real_trace _)
  calc
   _ = ‖Real.exp (t*(u-l)) • acts (quant T.sell) x‖ := by
     have heq : acts (quant T.sell) x = Real.exp (t*l) • acts (quant U.sell) x := quant_scaled p x hx U.sell t
     rw [heq,smul_smul, ←Real.exp_add,mul_sub, sub_add_cancel]
   _ ≤ Real.exp (t*(u-l)) * Real.exp m := by rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_mul_of_nonneg_left hy (Real.exp_pos _).le
   _ ≤ _ := by rw [←Real.exp_add]; apply Real.exp_monotone; unfold shellRent m a; dsimp only [d] at *; linarith only [hX]

#print axioms TiltSea
end YM.CF.WakeInvestment
