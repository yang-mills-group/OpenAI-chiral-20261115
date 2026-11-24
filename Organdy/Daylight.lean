import Organdy.Ink
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset


variable {ι τ:Type} [Fintype ι] [Fintype τ]

-- tensor of linear form, over constant charges
def pair (v w: τ→ℝ):ℝ:= ∑i,v i * w i
def square (v:τ→ℝ): τ×τ→ℝ:=fun i=> v i.1 * v i.2
lemma square_pair(v w:τ→ℝ): pair v w ^2= pair (square v) (square w):= by
 rw [pow_two,pair,sum_mul_sum,pair,Fintype.sum_prod_type]
 apply sum_congr rfl;intro i _
 apply sum_congr rfl;intro j _
 unfold square
 ring

-- scalar contraction
def fleet (a:ι→ℝ)(K:ι→ι→ℝ):ℝ:=∑i,∑j, a i * a j * K i j
lemma fleet_scalar(a:ι→ℝ)(V:ι→ℝ):
 fleet a (fun i j=>V i*V j)= (∑i,a i * V i)^2:=by
 rw [pow_two,sum_mul_sum,fleet]
 exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by ring
lemma fleet_mul(a:ι→ℝ)(K:ι→ι→ℝ)(c:ℝ):
 fleet a (fun i j=> c*K i j)= c*fleet a K:=by
 simp only [fleet,mul_sum]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by ring


variable (a:ι→ℝ)(v:ι→τ→ℝ)(d:τ→ℝ)
def glint : ℝ:=∑i,a i * (pair (v i) d)^2
def hue(t:τ×τ):ℝ:= ∑i,a i * square (v i) t

lemma glint_pair: glint a v d=pair (hue a v) (square d):=by
 simp_rw [glint,square_pair,pair,hue,mul_sum,sum_mul, mul_assoc]
 exact sum_comm

abbrev adore (a:ι→ℝ)(v:ι→τ→ℝ):ℝ:= fleet a (fun i j=> (pair (v i) (v j))^2)

lemma fleet_pair: adore a v= ∑t,hue a v t^2 := by
 simp_rw [adore,fleet,square_pair,pair,mul_sum]
 rw [show ∑i,∑j,∑t,a i*a j*(square (v i) t*square (v j) t)
       =∑i,∑t,∑j,a i*a j*(square (v i) t*square (v j) t)
       from sum_congr rfl (fun _ _=>sum_comm)]
 rw [sum_comm]
 exact sum_congr rfl fun _ _=>fleet_scalar ..

lemma uphold:0 ≤ adore a v:=by rw [fleet_pair];positivity

def floorCharge (d:τ→ℝ):ℝ:=1+ (∑t, square d t^2)
lemma floor_pos:0<floorCharge d:=by unfold floorCharge;positivity

lemma affluent: (glint a v d)^2 / floorCharge d ≤ adore a v:=by
 rw [div_le_iff₀ (floor_pos _),fleet_pair,glint_pair]
 unfold pair
 refine le_trans (sum_mul_sq_le_sq_mul_sq ..) ?_
 unfold floorCharge
 gcongr; exact le_add_of_nonneg_left zero_le_one

variable {a}
lemma skew {c ε:ℝ}(e:0≤ε)(g:∑i,|a i| ≤ c)
 (K H:ι→ι→ℝ)
 (p:∀i j,a i≠0→a j≠0→ |K i j-H i j|≤ ε):
  |fleet a K-fleet a H|≤ ε*c^2:=by
 have b(i j):|a i * a j * K i j - a i * a j * H i j| ≤ |a i| * |a j| * ε:=by
   rw [←mul_sub, abs_mul,abs_mul]
   by_cases x:a i=0
   · simp [x]
   by_cases y:a j=0
   · simp [y]
   exact mul_le_mul_of_nonneg_left (p _ _ x y) (by positivity)
 simp_rw [fleet,←sum_sub_distrib]
 refine le_trans (abs_sum_le_sum_abs ..) (le_trans
    (sum_le_sum (fun i _=> (abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _=>b i j))) ?_)
 rw [mul_comm ε]
 simp_rw [←sum_mul,←mul_sum,pow_two]
 have hp:0≤c:=g.trans' (by positivity)
 rw [←sum_mul];gcongr


lemma square_close (x y L ε:ℝ)(hε:0≤ε)(h:|x-y|≤ε)(k:|y|≤L):
 |2*x^2-2*y^2| ≤ 2*ε*(ε+2*L):=by
 rw [show 2*x^2-2*y^2=2*(x-y)*(x+y) by ring, abs_mul,abs_mul,abs_of_pos (by norm_num:0<(2:ℝ))]
 gcongr
 exact (abs_add_le ..).trans (by linarith [abs_sub_abs_le_abs_sub x y])

lemma fleet_add(a:ι→ℝ)(K H:ι→ι→ℝ):
 fleet a (fun i j=>K i j+H i j)=fleet a K+fleet a H:=by simp [fleet,mul_add,sum_add_distrib]

-- close to exact ideal incl scalar self arbitrary
variable (a)
lemma delight {c ε β:ℝ}(e:0≤ε)(g:∑i,|a i| ≤ c)
 (K:ι→ι→ℝ)(u:ι→ℝ)
 (p:∀i j,a i≠0→a j≠0→ |K i j-(u i*u j+2*β^2*(pair (v i) (v j))^2)|≤ ε):
  (2*β^2)*((glint a v d)^2/floorCharge d) - ε*c^2 ≤ fleet a K:=by
 have b:=abs_le.mp (skew e g _ _ p)
 rw [fleet_add, fleet_scalar, fleet_mul] at b
 linarith [mul_le_mul_of_nonneg_left (affluent a v d) (show 0≤2*β^2 by positivity),sq_nonneg (∑x,a x*u x)]
