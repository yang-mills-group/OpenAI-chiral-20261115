import YM.CF.Font.Trail
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Finset Filter
open scoped Topology BigOperators
variable {I J K:Type}[Fintype I][Fintype J][Fintype K]

/-- Finite coefficient ledgers. -/
abbrev Inky (I:Type) := I→I→ℝ
def soak (T:Inky I)(v:I→ℝ):=∑ i,∑ j,|T i j| *(v i*v j)
def dripQ (T:Inky I) (x y:I→ℝ):=∑ i,∑ j,T i j*(x i*y j)
def symmetric (T:Inky I):Prop:=∀ i j,T i j=T j i
def rebrand (F:I→J→ℝ)(T:Inky I):Inky J :=fun i j=>
  dripQ T (F · i) (F · j)
def laden (T:Inky I):= soak T 1

omit [Fintype K] in
lemma quad_commute (X:I→I→J→J→ℝ): (∑ i,∑ j,∑ a,∑ b,X i j a b)=(∑ a,∑ b,∑ i,∑ j,X i j a b):=by
 conv_lhs =>
   enter [2,i]
   rw [sum_comm]
 rw [sum_comm]
 apply sum_congr rfl; intro a _
 conv_lhs =>
   enter [2,i]
   rw [sum_comm]
 exact sum_comm -- binders?


lemma rebrand_drip (T:Inky I)(F:I→J→ℝ)(x y:J→ℝ):
    dripQ (rebrand F T) x y=dripQ T (fun i=>∑ j,F i j*x j) (fun i=>∑ j,F i j*y j):=by
 unfold rebrand dripQ
 conv_lhs =>
   enter [2,a,2,b]
   simp only [Finset.sum_mul]
 rw [quad_commute]
 apply sum_congr rfl; intro i _
 apply sum_congr rfl; intro j _
 rw [sum_mul,mul_sum]; apply sum_congr rfl; intro a _
 rw [mul_sum,mul_sum]; exact sum_congr rfl fun _ _=>by ring

omit [Fintype J] in
lemma rebrand_symm {T:Inky I} (h:symmetric T)(F:I→J→ℝ):symmetric (rebrand F T):=by
 intro a b; unfold rebrand dripQ
 rw [sum_comm]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>by rw [h,mul_comm (F j _)]

lemma laden_l (T:Inky I):laden T=∑ i,∑ j,|T i j|:= by simp [laden,soak]


lemma rebrand_laden (T:Inky I)(F:I→J→ℝ):
    laden (rebrand F T) ≤ soak T (fun i=>∑ j,|F i j|):=by
 rw [laden_l]
 let V(i j:I)(a b:J):= T i j*(F i a*F j b)
 refine le_trans (b:=∑ a,∑ b,∑ i,∑ j,|V i j a b|)
   (sum_le_sum fun a _=>sum_le_sum fun b _=>(abs_sum_le_sum_abs ..).trans (sum_le_sum fun _ _=> abs_sum_le_sum_abs ..)) ?_
 rw [quad_commute]; unfold soak
 apply sum_le_sum; intro i _
 apply sum_le_sum; intro j _
 rw [sum_mul,mul_sum]; apply sum_le_sum; intro a _
 rw [mul_sum,mul_sum]
 exact sum_le_sum fun _ _=>by simp only [V,abs_mul,le_refl]

lemma rebrand_wealth (T:Inky I)(F:I→J→ℝ)(p:I→ℝ)
   (h:∀ i,∑ j,|F i j|≤p i):
    laden (rebrand F T)≤ soak T p:=by
 have u(i):0≤∑ j,|F i j|:= sum_nonneg fun _ _=>abs_nonneg _
 refine (rebrand_laden T F).trans (sum_le_sum fun i _=>sum_le_sum fun j _=>
    mul_le_mul_of_nonneg_left (mul_le_mul (h i) (h j) (u j) ((u i).trans (h i))) (abs_nonneg _))


omit [Fintype J] in
lemma rebrand_vanish {T:Inky I}{F:I→J→ℝ}{a:J}
  (h:∀ i,F i a=0) (b):rebrand F T a b=0:=by simp [rebrand,dripQ,h]
lemma dripQ_quad (T:Inky I)(r:ℝ)(x:I→ℝ):
   dripQ T (r • x) (r • x)=r^2*dripQ T x x:=by
 unfold dripQ; simp_rw [Finset.mul_sum,Pi.smul_apply,smul_eq_mul]
 exact sum_congr rfl fun _ _=>sum_congr rfl fun _ _=>by ring

end YM.CF.Merino.Cuff
