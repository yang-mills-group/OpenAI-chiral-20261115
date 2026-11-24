import Organdy.Daylight
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset


variable {I τ:Type} [Fintype I] [Fintype τ]
/-- frequencies -/
abbrev Freq (I:Type):=I×I×Bool
def swing (p:Freq I):ℝ:=if p.2.2 then 1 else -1
def read (x:I→ℝ)(p:Freq I):ℝ:=x p.1+swing p*x p.2.1
def write (A:Ink I)(p:Freq I):ℂ:=A p.1 p.2.1*swing p/4

lemma level (p:Freq I):|swing p|=1:=by simp [swing,apply_ite (|·|)]
lemma score (A:Ink I)(x:I→ℝ): A.gilt x = ∑p, write A p*(read x p:ℂ)^2:=by
 rw [Ink.gilt,Fintype.sum_prod_type]
 refine sum_congr rfl fun i _=>?_
 rw [Fintype.sum_prod_type]
 refine sum_congr rfl fun j _=>?_
 simp [read,write,swing];ring

lemma tally (A:Ink I): (∑p, ‖write A p‖) ≤ A.qty:=by
 simp_rw [write,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,level]
 rw [Fintype.sum_prod_type,Ink.qty]
 apply sum_le_sum;intro i _
 rw [Fintype.sum_prod_type]
 apply sum_le_sum;intro j _
 norm_num
 linarith [norm_nonneg (A i j)]

lemma active {A:Ink I}{p:Freq I}(h:write A p≠0): A p.1 p.2.1≠0:=by
 intro e; apply h; simp [write,e]
lemma read_limit {p:Freq I}{y:I→ℝ}{c:ℝ} (h:|y p.1|≤c)(k:|y p.2.1|≤c):|read y p|≤2*c:=
  (abs_add_le ..).trans (by rw [abs_mul,level];linarith)

/-- two-sided expansion of any bilinear (not symmetric necessary) -/
def harmonics (C:I→I→ℝ)(p q:Freq I):ℝ:=
 read (fun i=> read (C i) q) p

lemma read_sub (x y:I→ℝ)(p:Freq I): read x p-read y p=read (fun i=>x i-y i) p:=by unfold read;ring
lemma read_mul(c:ℝ)(x:I→ℝ)(p:Freq I): c*read x p=read (fun i=>c*x i) p:=by unfold read;ring
lemma read_sum (y:τ→I→ℝ)(p:Freq I):
 (∑t, read (y t) p)= read (fun i=> ∑t,y t i) p:=by
   simp [read,sum_add_distrib,mul_sum]
lemma harmonics_mul(C:I→I→ℝ)(p q:Freq I)(t:ℝ):
 t*harmonics C p q=harmonics (fun i j=>t*C i j) p q:=by
   simp [harmonics,read_mul]

lemma harmonics_limit {C:I→I→ℝ}{p q:Freq I}{c:ℝ}
 (h:∀i∈({p.1,p.2.1}:Set I),∀j∈({q.1,q.2.1}:Set I),|C i j|≤c):
 |harmonics C p q|≤4*c:=by
 have x:∀i∈({p.1,p.2.1}:Set I), |read (C i) q| ≤ 2*c:=by
   intro i u; apply read_limit <;> exact h i u _ (by simp)
 rw [show 4*c=2*(2*c) by ring]
 unfold harmonics
 apply read_limit <;> exact x _ (by simp)

variable (π:I→τ)
open scoped Classical in
def bell (i:I)(t:τ):ℝ:=if t=π i then 1 else 0
-- avoid pi τ clashes? notation π scoped Real
def octave (p:Freq I)(t:τ):ℝ:= read (fun i=>bell π i t) p
lemma bell_pair (d:τ→ℝ)(i:I):pair (bell π i) d=d (π i):=by
 classical
 rw [pair]
 -- decider 
 rw [sum_eq_single (π i)]<;>simp [bell]
 exact fun b h j=> False.elim (h j)
lemma octave_pair(d:τ→ℝ)(p:Freq I):pair (octave π p) d=read (d ∘ π) p:=by
 simp only [octave,pair,mul_comm _ (d _),read_mul,read_sum]
 unfold read comp
 simp only [mul_comm (d _)]
 rw [←pair,←pair,bell_pair,bell_pair]
lemma seen (A:Ink I)(d:τ→ℝ):
   glint (fun i=>(write A i).re) (octave π) d=(A.gilt (d ∘ π)).re:=by
 rw [glint,score]
 simp only [octave_pair,←Complex.ofReal_pow,Complex.re_sum,Complex.mul_re]; simp only [Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero]

lemma duet_pair(p q:Freq I): pair (octave π p) (octave π q) =
 harmonics (fun i j=> bell π j (π i)) p q:=by
 rw [octave_pair,harmonics] -- uses π
 rfl
lemma bell_bound(i:I)(t:τ):|bell π i t| ≤1:=by unfold bell;split<;> norm_num
lemma duet_bound(p q:Freq I):|pair (octave π p) (octave π q)| ≤4 :=by
 rw [duet_pair]
 exact (harmonics_limit fun i _ j _=>bell_bound π j (π i)).trans_eq (mul_one _)

variable {E:Type} [NormedAddCommGroup E][InnerProductSpace ℝ E]
def combine (u:I→E)(p:Freq I):E:=u p.1+swing p • u p.2.1
lemma combine_bound{u:I→E}{p:Freq I}{b:ℝ}
    (h:‖u p.1‖≤b)(g:‖u p.2.1‖≤b):‖combine u p‖≤2*b:=
   (norm_add_le ..).trans (by rw [norm_smul, Real.norm_eq_abs, level];linarith)
lemma combine_spec(u:I→E)(p:Freq I)(x:E):
   inner ℝ (combine u p) x= read (fun i=>inner ℝ (u i) x) p:=by
    rw [combine, inner_add_left, real_inner_smul_left,read]
lemma combine_duet(u v:I→E)(p q:Freq I):
   inner ℝ (combine u p) (combine v q)=
    harmonics (fun i j=>inner ℝ (u i) (v j)) p q:=by
   rw [combine_spec]; unfold harmonics
   congr;ext i
   rw [real_inner_comm,combine_spec];simp [real_inner_comm]
