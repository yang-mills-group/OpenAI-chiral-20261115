import Merino.Garter.Guard
import Merino.Garter.Silver
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

abbrev glint(q:Clip):=(Real.sqrt q.direct)⁻¹
lemma holm(q:Clip):0<glint q:= inv_pos.mpr (Real.sqrt_pos.2 q.quadratic_pos)

lemma silver_length (q:Clip)(a:StepIn n)(i:Husk G n)(x:Altar G n): 
   |silver q a i x|=glint q* |x (a.sent i.1,false,i.2)|:=by
 rw [silver_at,abs_mul,show |a.cost i.1|=1 from orient_abs ..,one_mul]
 change |glint q*_|=_
 rw [abs_mul,abs_of_pos (holm q)]; rfl

universe v'
lemma scattered {J:Type v'} [Fintype J] [DecidableEq J]
 (x:EuclideanSpace ℝ J) [Fintype I] (j:I→J)(h:Injective j):
 ∑ i, |x (j i)| ≤ Real.sqrt (Fintype.card I) * ‖x‖:=by
 have t:(∑i, |x (j i)|^2)≤ ‖x‖^2:=by
   rw [EuclideanSpace.real_norm_sq_eq]
   refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image j)) (fun k _ _ =>sq_nonneg _))
   rw [sum_image h.injOn]
   simp only [sq_abs,le_rfl]
 have u:= Real.sum_mul_le_sqrt_mul_sqrt univ (fun i:I=>1) (fun i=>|x (j i)|)
 exact le_trans (by simpa using u)
   (mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt t).trans_eq (Real.sqrt_sq (norm_nonneg x))) (Real.sqrt_nonneg _))


abbrev gleamC(q:Clip):=(Fintype.card Signed:ℝ)*glint q
lemma gleamC_non(q:Clip):0≤gleamC q:=mul_nonneg (Nat.cast_nonneg _) (holm q).le

variable [Fintype I] {z:I→StepIn n}{k:ℕ}
lemma silver_toll (q:Clip)(tz:Packs k z)
 (i:Husk G n)(x:Altar G n):
 ∑ j, |silver q (z j) i x|≤
   gleamC q*Real.sqrt (Fintype.card I)*‖x‖:=by
 let p(s:Signed)(j:I):= ((StepIn.mk s (z j).there).sent i.1,false,i.2)
 have h(s):Injective (p s):= 
   fun _ _ he=>tz.unique ((sent_unique _ _) (congrArg Prod.fst he))
 simp_rw [silver_length]
 rw [← mul_sum]
 have t:∑ j, |x ((z j).sent i.1,false,i.2)|≤ ∑ s:Signed,∑ j:I, |x (p s j)|:=by
   rw [sum_comm (α:=I)] -- params?
   apply sum_le_sum; intro j _
   exact single_le_sum (f:=fun s=>|x (p s j)|) (fun _ _=>abs_nonneg _) (mem_univ (z j).face)
 refine (mul_le_mul_of_nonneg_left (t.trans (sum_le_sum fun s _=>scattered x _ (h s))) (holm q).le).trans_eq ?_
 rw [sum_const,card_univ,nsmul_eq_mul]; unfold gleamC; ring


omit [Fintype I] in
lemma silver_norm(q:Clip)(a:StepIn n)(i:Husk G n)(x:Altar G n):
   |silver q a i x| ≤ glint q*‖x‖:=by
 rw [silver_length]
 refine mul_le_mul_of_nonneg_left ?_ (holm q).le
 rw [← one_mul (‖x‖)]
 simpa using scattered x (fun _:Unit=>(a.sent i.1,false,i.2)) (fun _ _ _=>by exact Subsingleton.elim ..)

end YM.CF.Merino.Garter
