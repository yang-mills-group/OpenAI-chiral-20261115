import Merino.Garter.Bar
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Garter
open Cuff Finset Function
open scoped BigOperators ContDiff
open MeasureTheory

variable {J:Type}[Fintype J]{T:Inky J}

/-- expands two coupons in the order i,j,k,l -/
abbrev batches (T:Inky J)(F:J→J→J→J→ℝ):=pour T fun i k=>pour T (F i k)
lemma batches_add(f g:J→J→J→J→ℝ):
    batches T (fun i j k l=>f i j k l+g i j k l)=batches T f+batches T g:=by
   simp only [batches,pour,mul_add,sum_add_distrib]
lemma batches_sub(f g:J→J→J→J→ℝ):
    batches T f-batches T g=batches T (fun i j k l=>f i j k l-g i j k l):=by
   simp only [batches,pour,mul_sub,sum_sub_distrib]
lemma batches_scale(f:J→J→J→J→ℝ)(a:ℝ):
   batches T (fun i j k l=>a*f i j k l)=a*batches T f:=by
  unfold batches pour
  simp_rw [mul_sum]
  exact sum_congr rfl fun _ _ =>sum_congr rfl fun _ _ => sum_congr rfl
     fun _ _=>sum_congr rfl fun _ _=>by ring
variable {L K:ℝ}


lemma batches_abs (q:laden T≤L)(s:0≤K) (f:J→J→J→J→ℝ)
    (p:∀ i j k l,T i j≠0 → T k l≠0 → |f i j k l|≤K): |batches T f|≤L^2*K:=by
 have t:0≤L:= le_trans (by rw [laden_l]; positivity) q
 rw [pow_two,mul_assoc]
 exact pour_abs _ (mul_nonneg t s) q fun i j a=> pour_abs _ s q
     fun k l b=> p i j k l a b
lemma batches_prod(f g:J→J→ℝ):
 batches T (fun i j k l=>f i j*g k l)=pour T f*pour T g:=by
 unfold batches pour
 simp_rw [sum_mul,mul_sum]
 -- rearrangements?
 exact sum_congr rfl fun _ _ =>sum_congr rfl fun _ _ => sum_congr rfl
    fun _ _=>sum_congr rfl fun _ _=>by ring

section
variable {E:Type} [MeasurableSpace E]{μ:Measure E}
lemma pour_int (f:E→J→J→ℝ)(v:∀ i j,Integrable (fun x=>f x i j) μ):
 Integrable (fun x=>pour T (f x)) μ:=integrable_finsetSum _ fun i _=>
    integrable_finsetSum _ fun j _=>(v i j).const_mul _
lemma pour_pull (f:E→J→J→ℝ)(v:∀ i j,Integrable (fun x=>f x i j) μ):
 (∫ x,pour T (f x)∂μ)=pour T (fun i j=>∫ x,f x i j∂μ):=by
 unfold pour
 rw [integral_finsetSum _ (fun _ _=>integrable_finsetSum _ fun _ _=>(v _ _).const_mul _)]

 exact sum_congr rfl fun i _=> by
    rw [integral_finsetSum _ (fun _ _=>(v _ _).const_mul _)]
    simp_rw [integral_const_mul]
lemma batches_int (f:E→J→J→J→J→ℝ)
 (v:∀ i j k l,Integrable (fun x=>f x i j k l) μ):
  Integrable (fun x=>batches T (f x)) μ:=
  pour_int (fun x i j=>pour T (f x i j)) fun i j=>pour_int _ (v i j)
lemma batches_pull(f:E→J→J→J→J→ℝ)
 (v:∀ i j k l,Integrable (fun x=>f x i j k l) μ):
 (∫ x,batches T (f x)∂μ)=batches T (fun i j k l=>∫ x,f x i j k l∂μ):=by
  have t(i j): Integrable (fun x=>pour T (f x i j)) μ:=pour_int _ (v i j)
  unfold batches
  rw [pour_pull (fun x i j=>pour T (f x i j)) t]
  congr 1; funext i j
  exact pour_pull _ (v i j)
end

end YM.CF.Merino.Garter
