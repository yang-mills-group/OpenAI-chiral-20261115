import Merino.Garter.Luster
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Garter
open Function Lattice Finset RG Wilson Metric Exterior Work.F03
open Regis.Head MeasureTheory
open scoped Topology ContDiff InnerProductSpace Classical Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}

open Cuff Hem
variable {I:Type*}
open Tree Filter Precision Next.Rank.Spindle Pressure ProbabilityTheory
open Gleam Next.SectorChange Next.SectorChange.Gaussian
open Etch -- (includes river)
open StepIn
variable {c:Side}{r:Ratio c n}{H:Bed}{m:ℕ}{p:BudgetPoint}{q:Clip}{v η S C δ w β:ℝ}{A:Support c}{N:Finset (Cell n)}{Z:PathData G}

open scoped NNReal
variable {L M:ℝ}{k:ℕ}{T:Bundle G n}

abbrev shine (q:Clip)(d:ℝ)(a:StepIn n)(x:Altar G n)(i:Husk G n):ℝ:=
 bite d (silver q a i x)
abbrev gleam (T:Bundle G n)(q:Clip)(d:ℝ)(a:StepIn n)(x:Altar G n):ℝ:=
 dripQ T (shine q d a x) (shine q d a x)
abbrev couple (T:Bundle G n)(q:Clip)(d:ℝ)(g:Duo n)(x:Altar G n):ℝ:=
 gleam T q d g.1 x * gleam T q d g.2 x
def displayBoard (T:Bundle G n)(q:Clip)(d:ℝ)(g:Duo n)[Fintype I](j:I→StepIn n)(z:ℝ)(x:Altar G n):ℝ:=
 z *∑ i,couple T q d ((j i).rotate g) x

lemma gleam_zero (q:Clip)(a:StepIn n)(x:Altar G n):
 gleam T q 0 a x = gloss T q a x:=by simp [gleam,shine,bite,dripQ,gloss]


lemma gleam_free (q:Clip)(t:laden T≤L)(s:0<M)(a:StepIn n)(x:Altar G n): 
  |gleam T q M⁻¹ a x|≤L*M^2:=
 splash _ t (fun _ _ _=>⟨chew_bound s _,chew_bound s _⟩)
lemma gleam_smooth(q:Clip)(d)(a:StepIn n): ContDiff ℝ 1 (gleam T q d a):=by
 unfold gleam dripQ shine
 exact ContDiff.sum (fun _ _=>ContDiff.sum fun _ _=>contDiff_const.mul
    (((chew_smooth _).comp (silver .. |>.contDiff)).mul
       ((chew_smooth _).comp (silver ..|>.contDiff))))
lemma couple_free(q:Clip)(t:laden T≤L)(s:0<M)(g:Duo n)(x:Altar G n):
 |couple T q M⁻¹ g x|≤(L*M^2)^2:= by
 unfold couple; rw [abs_mul,pow_two]
 exact mul_le_mul (gleam_free _ t s ..) (gleam_free _ t s ..) (abs_nonneg _)
  ((abs_nonneg _).trans (gleam_free q t s g.1 x))
lemma couple_smooth(q:Clip)(d)(g:Duo n): ContDiff ℝ 1 (couple T q d g):=
 (gleam_smooth ..).mul (gleam_smooth ..)


variable [Fintype I] 
lemma board_free(q:Clip)(t:laden T≤L)(s:0<M)(g:Duo n)(j:I→StepIn n)(z:ℝ)(x:Altar G n):
 |displayBoard T q M⁻¹ g j z x|≤ |z| *(Fintype.card I*((L*M^2)^2)):=by
  unfold displayBoard; rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans ((sum_le_sum
     (fun i _ => couple_free q t s ((j i).rotate g) x)).trans_eq ?_)) (abs_nonneg _)
  simp
lemma board_smooth(q:Clip)(d)(g:Duo n)(j:I→StepIn n)(z:ℝ):
 ContDiff ℝ 1 (displayBoard T q d g j z):=
 contDiff_const.mul (ContDiff.sum fun _ _=> couple_smooth ..)

lemma gleam_toll (q:Clip)(t:laden T≤L)(s:0 < M)
 (j:I→StepIn n)(tj:Packs k j)(x y:Altar G n):
 ∑ i,|gleam T q M⁻¹ (j i) x - gleam T q M⁻¹ (j i) y|
    ≤ L*(2*M*(gleamC q*Real.sqrt (Fintype.card I)*‖x-y‖)):=by
  apply spray t _ _ s.le (mul_nonneg (mul_nonneg (gleamC_non _) (Real.sqrt_nonneg _)) (norm_nonneg _))
    (fun _ _=>chew_bound s _) (fun _ _=>chew_bound s _)
  intro i
  apply (silver_toll q tj i (x-y)).trans'
  simp only [map_sub]
  exact sum_le_sum fun _ _=>chew_soft _ _ _


def salt(q:Clip)(L:ℝ):ℝ:=4*L^2*gleamC q
lemma board_toll (q:Clip)(t:laden T≤L)(s:0<M)(h:0≤L)
 {g:Duo n}{j:I→StepIn n}(u:Pavilion k g j)(z:ℝ)(x:Altar G n):
 ‖fderiv ℝ (displayBoard T q M⁻¹ g j z) x‖ ≤ 
    salt q L * M^3*|z| * Real.sqrt (Fintype.card I):=by
 let l:ℝ≥0:=⟨salt q L*M^3*|z| *Real.sqrt (Fintype.card I),
     by have c:=gleamC_non q; unfold salt; positivity⟩
 apply norm_fderiv_le_of_lipschitz (C:=l) ℝ
 refine LipschitzWith.of_dist_le_mul fun x y=>?_
 rw [dist_eq_norm,dist_eq_norm,Real.norm_eq_abs]
 unfold displayBoard; rw [← mul_sub,abs_mul,←sum_sub_distrib]
 let C:=L*(2*M*(gleamC q*Real.sqrt (Fintype.card I)*‖x-y‖))
 have c: ∑ i,|couple T q M⁻¹ ((j i).rotate g) x - couple T q M⁻¹ ((j i).rotate g) y|
     ≤ 2*(L*M^2)*C:=by
   let ā (x:Altar G n)(p:StepIn n)(i:I):=gleam T q M⁻¹ (j i*p) x
   exact blemish (ā x g.1) (ā x g.2) (ā y g.1) (ā y g.2)
     (by positivity) (fun i=>gleam_free _ t s ..) (fun i=>gleam_free _ t s ..)

     (gleam_toll q t s _ u.1 x y) (gleam_toll q t s _ u.2 x y)
 apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans c)
      (abs_nonneg _)).trans
 change _ ≤ salt q L*M^3*|z| *Real.sqrt (Fintype.card I)*‖x-y‖
 unfold C salt
 apply le_of_eq
 ring

end YM.CF.Merino.Garter
