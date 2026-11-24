import YM.SU5.FiniteGaugeData.Brique.Frequency
import YM.SU5.FiniteGaugeData.Brique.Screw
import YM.SU5.FiniteGaugeData.Largo.Prill
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N : Side} {k:ℕ} {d b:ℝ}
section spin
private lemma unity3 : gammaOp 0*gammaOp 1*gammaOp 2*grading= -gammaOp 3 := by
 -- use gradingSwap simpler grading * gamma3 = gamma.. mod gamma3²→
 have he:grading*gammaOp 3=gammaOp 0*gammaOp 1*gammaOp 2:=by nth_rw 1 [grading_rule]; rw [mul_assoc (gammaOp 0*gammaOp 1*gammaOp 2), gammaOne,mul_one]
 rw [←he,gradingSwap,neg_mul,mul_assoc, gradingOne,mul_one]
def ChiT : UNI SpinIdx:= pinLift 0 * pinLift 1 * pinLift 2
lemma ChiT_vis : ChiT.val= gammaOp 3:=by
 set a:= gammaOp 0; set b:= gammaOp 1; set c:=gammaOp 2; set t:=grading
 change a*t*(b*t)*(c*t)=_; rw [←mul_assoc _ b t, mul_assoc a,show t*b=-(b*t) from gradingSwap _,mul_neg,neg_mul,neg_mul,←mul_assoc a b t, mul_assoc (a*b) t,show t*t=1 from gradingOne,mul_one,← mul_assoc,show a*b*c*t = _ from unity3, neg_neg]
-- symbols tables. k natural including > etc.
variable (x : Momentum) (y:ℂ)
lemma ink : zen x= !![0,0,x 2+Complex.I*x 3,x 0-Complex.I*x 1; 0,0,x 0+Complex.I*x 1, -x 2+Complex.I*x 3; -x 2+Complex.I*x 3,-x 0+Complex.I*x 1,0,0; -x 0-Complex.I*x 1, x 2+Complex.I*x 3,0,0]:= by
 ext i j; fin_cases i <;> fin_cases j <;> norm_num [zen,gammaOp, Fin.sum_univ_succ,Axis] <;> (try simp only [show (3:Fin 4)=Fin.succ 2 from rfl]) <;> ring
-- world formula
local notation "ℊ"=> Op SpinIdx
def look (A:ℂ)(r: Momentum): Op SpinIdx := !![A,0,r 2+Complex.I*r 3,r 0-Complex.I*r 1;
               0,A,r 0+Complex.I*r 1, -r 2+ Complex.I*r 3;
               r 2-Complex.I*r 3,r 0-Complex.I*r 1,1-A,0;
               r 0+Complex.I*r 1,-r 2-Complex.I*r 3,0,1-A]
lemma bar_look (k:ℕ)(M:Side) (x: Momentum) : bar k M x= look (shell k M x) (skin k M x):=by
 unfold bar; rw [ink]; ext i j; fin_cases i <;>fin_cases j<;> norm_num [grading, look, SpinIdx, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
section slots
variable (A: Op SpinIdx)
local notation "UB"=> (0 : SpinIdx)
local notation "FiniteGaugeData"=> (3: SpinIdx)
local notation "P"=> cutM {UB}
local notation "Q"=> cutM {FiniteGaugeData}
local notation "B"=> look y x
local notation "H"=> 1-B
-- gamma3 kicks by exact permutation, avoid Fin table prints
abbrev W (x:ℊ):= twist ChiT x
-- par2 involution
def par2 (i:SpinIdx) : SpinIdx:= match i with | 0=>2|1=>3|2=>0|3=>1
lemma par_inv (i:SpinIdx): par2 (par2 i)=i:=by revert i; decide
lemma gama_app (A:Op SpinIdx)(i j:SpinIdx): W A i j=A (par2 i) (par2 j):=by
 rw [W,twist_formula,ChiT_vis,(gammaAdj _).star_eq]; have he (x y:SpinIdx): gammaOp 3 x y=if y=par2 x then 1 else 0:=by
    fin_cases x<;>fin_cases y <;> first| (rw [if_pos (by decide)]; rfl)| (rw [if_neg (by decide)]; rfl)
 rw [Matrix.mul_apply,sum_eq_single (par2 j)]; swap; · intro b _ p; rw [he,if_neg (by intro h; exact p (par_inv b ▸ congrArg par2 h.symm)) ,mul_zero]
 swap; · simp
 rw [he, if_pos (par_inv j).symm,mul_one, Matrix.mul_apply,sum_eq_single (par2 i)]; rw [he,if_pos rfl,one_mul]; intro b _ p; simp [he,p]; simp
lemma minus_mem (i:SpinIdx) : i∈plusHalfᶜ ↔ i=2 ∨ i=3 := by revert i; decide
lemma dawnG : W (look y x) 2 3= 0 ∧ W (look y x) 3 3=y ∧ W (look y x) 0 3=x 0-Complex.I*x 1 :=by simp only [gama_app]; exact ⟨rfl,rfl,rfl⟩
private lemma formula0 (T:Op SpinIdx)(h:T 2 3=0)(z:T 3 3=y): cutM plusHalfᶜ * T * Q = y • Q:=by
 ext i j; rw [cutM,cutM, Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases p:j=(3:SpinIdx)
 · subst j; by_cases t:i∈plusHalfᶜ
   · rcases (minus_mem i|>.mp t) with a|b
     · subst i; rw [if_pos t,h,mul_zero,zero_mul]; simp [Matrix.diagonal_apply_ne, show (2:SpinIdx)≠3 by decide]
     subst i; rw [if_pos t]; simp [z]
   have hi:i≠3:=fun a=>t ((minus_mem ..).2 (Or.inr a))
   rw [if_neg t,zero_mul,zero_mul]; simp [Matrix.diagonal_apply_ne,hi]
 by_cases w:i=j; · subst i; simp [p,Matrix.diagonal_apply]
 simp [p,Matrix.diagonal_apply,w]
lemma low_formula : cutM plusHalfᶜ * (1-look y x)*cutM {(3:SpinIdx)}= y • Q:= by
 refine formula0 y _ ?_ ?_; rw [Matrix.sub_apply,Matrix.one_apply_ne (by decide), show look y x 2 3=0 from rfl,sub_zero]; rw [Matrix.sub_apply,Matrix.one_apply_eq,show look y x 3 3=1-y from rfl]; abel
lemma low_formulaP : cutM plusHalfᶜ * (W (look y x))*Q= y • Q:= formula0 y _ (dawnG x y).1 (dawnG x y).2.1
lemma mid_formulaP : P * (1-look y x)* Q= -(P* W (look y x)*Q):=by
 ext i j; simp only [cutM, Matrix.mul_diagonal,Matrix.diagonal_mul, Matrix.neg_apply]; by_cases v:i=(0:SpinIdx); swap; simp [v]
 by_cases t:j=(3:SpinIdx); swap; simp [t]
 subst i j; simp only [mem_singleton,if_pos, Matrix.sub_apply, mul_one,one_mul,(dawnG x y).2.2, Matrix.one_apply_ne (show (0:SpinIdx)≠3 from by decide),zero_sub]; rfl
-- parse Spin choose. 
variable (k:ℕ)(M:Side)(r:Momentum)
private lemma cut_single (A:Op SpinIdx)(i j p:SpinIdx): (A*cutM {i}*A) j p=A j i*A i p:=by rw [Matrix.mul_apply,sum_eq_single i,cutM,Matrix.mul_diagonal]; simp; intro b _ w; simp [cutM,Matrix.mul_diagonal,w]; simp
lemma left_norm : ( (1-bar k M r)*Q*(1-bar k M r)) UB UB=(skin k M r 0)^2+(skin k M r 1)^2:=by
 rw [cut_single,bar_look, Matrix.sub_apply,Matrix.sub_apply,Matrix.one_apply_ne (by decide),Matrix.one_apply_ne (by decide)]; let x:=skin k M r 0; let y:=skin k M r 1; change (0-(x-Complex.I*y))*(0-(x+Complex.I*y))=x^2+y^2; ring_nf; simp
lemma bottom_norm : ((1-bar k M r)*Q*(1-bar k M r)) FiniteGaugeData FiniteGaugeData=(shell k M r)^2:=by rw [cut_single,bar_look,Matrix.sub_apply,Matrix.one_apply_eq]; let x:=shell k M r; change (1-(1-x))*(1-(1-x))=x^2; ring
lemma cross_norm : ((1-bar k M r)*Q*(1-bar k M r)) UB FiniteGaugeData=(shell k M r)*(- (skin k M r 0)+Complex.I*(skin k M r 1)):=by rw [cut_single,bar_look,Matrix.sub_apply,Matrix.sub_apply,Matrix.one_apply_ne (by decide),Matrix.one_apply_eq]; let x:=skin k M r 0; let y:=skin k M r 1; let z:=shell k M r; change (0-(x-Complex.I*y))*(1-(1-z))=z*(-x+Complex.I*y); ring
end slots
#print axioms cross_norm
end spin
end YM.CF.Window.Pivot
