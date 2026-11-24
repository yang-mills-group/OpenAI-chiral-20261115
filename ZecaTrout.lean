import ZecaFinray
import ZecaLamprey
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology


-- source ℤ difference on a Hilbert chain. 
variable {H:Type*}[NormedAddCommGroup H][InnerProductSpace ℂ H]

def splashing(x:ℤ→H):ℕ→ℤ→H
 | 0=>x
 | n+1=>fun k=>splashing x n (k+1) - splashing x n k
variable (x:ℕ→ℤ→H) (h:ℝ) (f:ℝ→ℂ)
def knocks : Prop:=
 ∀i j:ℤ,
 Tendsto (fun n=>inner ℂ (x n i) (x n j)) atTop (𝓝 (f ((j-i:ℝ)*h)))

abbrev thrown(h:ℝ)(f:ℝ→ℂ) (k:ℕ) (a b:ℤ):ℂ:=
 (-1:ℂ)^k*fstroke h f (2*k) ((b-a-(k:ℝ))*h)

lemma thrown_step (k:ℕ) (a b:ℤ):
 ((thrown h f k (a+1) (b+1) - thrown h f k a (b+1)) -
   (thrown h f k (a+1) b - thrown h f k a b)) =
 thrown h f (k+1) a b:=by
 unfold thrown 
 rw [show 2*(k+1)= (2*k+1)+1 from by ring,fstroke,fstroke]
 push_cast
 ring_nf
 <;> ring

lemma trout (p:knocks x h f)
 (k:ℕ) (a b:ℤ):
 Tendsto (fun n=>inner ℂ (splashing (x n) k a) (splashing (x n) k b))
   atTop (𝓝 (thrown h f k a b)):=by
 induction k generalizing a b with
 | zero =>
    simpa only [thrown,Int.cast_ofNat,Nat.cast_zero,sub_zero,pow_zero,one_mul,
      mul_zero,fstroke,splashing] using p a b
 | succ k i =>
    rw [← thrown_step]
    apply Tendsto.congr _
     (((i (a+1) (b+1)).sub (i a (b+1))).sub ((i (a+1) b).sub (i a b)))
    intro n
    rw [splashing,inner_sub_right,inner_sub_left,inner_sub_left]
lemma troutSq (p:knocks x h f) (k:ℕ):
 Tendsto (fun n=>‖splashing (x n) k 0‖^2)
   atTop (𝓝 (‖fstroke h f (2*k) (-(k:ℝ)*h)‖)):=by
 have v:=(trout x h f p k 0 0).norm
 rw [show (‖thrown h f k 0 0‖)=‖fstroke h f (2*k) (-(k:ℝ)*h)‖ from by simp [thrown]] at v
 refine v.congr fun n=>?_
 rw [inner_self_eq_norm_sq_to_K]
 simp
#print axioms troutSq
